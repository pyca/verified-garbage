import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect

/-!
# `vg_rsa_private_checked` on x86-64: constant time

Two runs from entry states that agree on the public data (`chkContract.pub`:
the pointers and lengths, `n` and `e`) leak the same trace. Each point of
the code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`): the blocks between the calls are checked by the taint analysis
from the registers this fixes, and each call is constant time for its
callee's contract, whose public data it fixes too (`body_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := chkContract.pre s ∧ chkContract.pub a s

theorem pub_refl (s : State) : chkContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 14) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.n {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.1.symm

theorem Sib.e {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- In the frame, `rsp` is public. -/
theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb (fun s t h => (hJ s t h).rsp) (fun _ _ h => h.fb) h₁ h₂

theorem Env.congr {s t t' : State} (he : Env s t) (hm : t'.mem = t.mem) (hk : Keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] t t') :
    Env s t' :=
  ⟨(hk.gpr (by decide)).trans he.rsp, hk.2.1.trans he.rd, hk.2.2.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut,
    hm ▸ he.sN, hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

/-- A caller's buffer, read by a callee: the same as at the entry. -/
theorem Env.entryBytes {s t : State} (he : Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)) hk ho hs hl

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = allocState frameBytes s

def J1 (s t : State) : Prop :=
  Env s t ∧ (∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2)) ∧ t.gpr .rdi = off (fb s) oM ∧
    t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧
    t.gpr .r9 = s.gpr .rcx

def J2 (s t : State) : Prop := Env s t

def J3 (s t : State) : Prop :=
  Env s t ∧ t.gpr .rdi = off (fb s) oPre ∧
    t.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 12 ∧ t.gpr .r9 = stackArg s 13

/-- The precomputed values of `n`, or zeros. -/
def preVal (nB : List Byte) (w : Nat) : List (BitVec 64) :=
  match Spec.Rsa.publicPrecompute nB with
  | some ws => ws
  | none => List.replicate w 0

def J4 (s t : State) : Prop :=
  Env s t ∧ Spec.Rsa.wordsAt t.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
    preVal (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)

def J5 (s t : State) : Prop :=
  J4 s t ∧ word t.mem (fb s) 0 = off (fb s) oM ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
    word t.mem (fb s) 16 = stackArg s 12 ∧ word t.mem (fb s) 24 = stackArg s 13 ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = off (fb s) oPre ∧
    t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

def J7 (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = stackArg s 0 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .r10 = BitVec.ofNat 64 0

/-! ## The calls -/

/-- The registers a callee sees, from the caller's. -/
theorem entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

theorem regs_eq {s₁ s₂ : State}
    (h : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₁.gpr = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₂.gpr) :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp h

/-- What the CRT's contract makes public, from the entry state. -/
theorem crt_view {a s t : State} (S : Sib a s) (h : J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (crtRd s) (crtWr s)).gpr =
      [off (fb a) oM, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, stackArg a 0, a.gpr .rcx, fb a - 8] ∧
    (∀ i < 12, stackArg (t.callEntry.withRegions (crtRd s) (crtWr s)) i = stackArg a (i + 2)) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (crtRd s) (crtWr s)).mem
      ((t.callEntry.withRegions (crtRd s) (crtWr s)).gpr .rdx)
      ((t.callEntry.withRegions (crtRd s) (crtWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preF_of S.1
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by omega), hargs i hi, S.arg (by omega)]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [he.entryBytes _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]

theorem crt_ct (v : CrtImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := crtContract.clear) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, n₁⟩ := crt_view S₁ j₁
  obtain ⟨r₂, g₂, n₂⟩ := crt_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := crt_covers (preF_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := crt_covers (preF_of S₂.1) j₂.1
  obtain ⟨he₁, hargs₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hargs₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : crtContract.clear.pre ((t₁.callEntry).withRegions (crtRd s₁) (crtWr s₁)) :=
    ⟨crt_pre (preF_of S₁.1) he₁ hargs₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁, crt_clear (preF_of S₁.1) he₁⟩
  have p₂ : crtContract.clear.pre ((t₂.callEntry).withRegions (crtRd s₂) (crtWr s₂)) :=
    ⟨crt_pre (preF_of S₂.1) he₂ hargs₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂, crt_clear (preF_of S₂.1) he₂⟩
  have ga : ∀ i < 12, stackArg ((t₁.callEntry).withRegions (crtRd s₁) (crtWr s₁)) i =
      stackArg ((t₂.callEntry).withRegions (crtRd s₂) (crtWr s₂)) i := fun i hi => (g₁ i hi).trans (g₂ i hi).symm
  have hpub : crtContract.pub ((t₁.callEntry).withRegions (crtRd s₁) (crtWr s₁))
      ((t₂.callEntry).withRegions (crtRd s₂) (crtWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide),
      ga 4 (by decide), ga 5 (by decide), ga 6 (by decide), ga 7 (by decide), ga 8 (by decide), ga 9 (by decide),
      ga 10 (by decide), ga 11 (by decide), n₁.trans n₂.symm⟩
  exact ⟨crtRd s₁, crtWr s₁, crtRd s₂, crtWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precompute`'s contract makes public. -/
theorem pc_view {a s t : State} (S : Sib a s) (h : J3 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map
        (t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [preR s, scrR s]).gpr =
      [off (fb a) oPre, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat), a.gpr .rdx, a.gpr .rcx,
        stackArg a 12, stackArg a 13, fb a - 8] ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [preR s, scrR s]).mem
      ((t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [preR s, scrR s]).gpr .rdx)
      ((t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [preR s, scrR s]).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preF_of S.1
  refine ⟨?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide), S.arg (by decide)]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [he.entryBytes _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]

theorem pc_ct (pc : Prog isa) (name : String)
    (hok : ∀ s, pcContract.clear.pre s → ∃ t s', Exec isa pc s t s' ∧ abiPreserved s s' ∧ pcContract.post s s')
    (hct : ConstantTime isa pcContract.clear.pre pcContract.pub pc) :
    RelCT isa (Two (At J3)) (.call name pc) fun _ _ => True := by
  refine RelCT.callEx (k := pcContract.clear) hok hct
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, n₁⟩ := pc_view S₁ j₁
  obtain ⟨r₂, n₂⟩ := pc_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pc_covers (preF_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := pc_covers (preF_of S₂.1) j₂.1
  obtain ⟨he₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  exact ⟨_, _, _, _, pc_pre (preF_of S₁.1) he₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁,
    pc_pre (preF_of S₂.1) he₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂, ⟨regs_eq (r₁.trans r₂.symm), n₁.trans n₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precomputed_checked`'s contract makes public. -/
theorem pd_view {a s t : State} (S : Sib a s) (h : J5 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pdRd s) (pdWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, off (fb a) oPre, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat),
        a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (pdRd s) (pdWr s)) 0 = off (fb a) oM ∧
    stackArg (t.callEntry.withRegions (pdRd s) (pdWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (pdRd s) (pdWr s)) 2 = stackArg a 12 ∧
    stackArg (t.callEntry.withRegions (pdRd s) (pdWr s)) 3 = stackArg a 13 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (pdRd s) (pdWr s)).mem
      ((t.callEntry.withRegions (pdRd s) (pdWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pdRd s) (pdWr s)).gpr .rcx).toNat =
      preVal (Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat)
        (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pdRd s) (pdWr s)).mem
      ((t.callEntry.withRegions (pdRd s) (pdWr s)).gpr .r8)
      ((t.callEntry.withRegions (pdRd s) (pdWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨⟨he, hpw⟩, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preF_of S.1
  have hk2 := hp.k2
  have hpwl := preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have rcx := S.gpr (r := .rcx) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, rcx, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.fb]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← rcx]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, hcxN]
    rw [entry_words he.rsp (show oPre + 8 * Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ frameBytes by
      unfold oPre frameBytes; omega), hpw, S.n, rcx]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [he.entryBytes _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S.e]

theorem pd_ct (P : PublicImpl) (name : String) :
    RelCT isa (Two (At J5)) (.call name (P.code)) fun _ _ => True := by
  have hct : ConstantTime isa (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pub (P.code) :=
    P.ct
  refine RelCT.callEx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩)
    P.ok hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, w₁', e₁⟩ := pd_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, w₂', e₂⟩ := pd_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pd_covers (preF_of S₁.1) j₁.1.1
  obtain ⟨c₂, w₂⟩ := pd_covers (preF_of S₂.1) j₂.1.1
  obtain ⟨⟨he₁, -⟩, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨⟨he₂, -⟩, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : pdContract.pre (t₁.callEntry.withRegions (pdRd s₁) (pdWr s₁)) :=
    pd_pre (preF_of S₁.1) he₁ hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ : pdContract.pre (t₂.callEntry.withRegions (pdRd s₂) (pdWr s₂)) :=
    pd_pre (preF_of S₂.1) he₂ hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdContract.pub (t₁.callEntry.withRegions (pdRd s₁) (pdWr s₁))
      (t₂.callEntry.withRegions (pdRd s₂) (pdWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, w₁'.trans w₂'.symm, e₁.trans e₂.symm⟩
  exact ⟨pdRd s₁, pdWr s₁, pdRd s₂, pdWr s₂, p₁, p₂, hpub, Covers.append_left c₁ w₁.right, w₁,
    Covers.append_left c₂ w₂.right, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem crtArgs_two : RelCT isa (Two (At J0)) (.block crtArgs) (Two (At J1)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin fb (fun s t h => by rw [h]; rfl) (fun _ _ h => h.fb) h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      subst ht
      exact WP.mono (crtArgs_ok (preF_of S.1)) fun _ ⟨he, _, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ =>
        ⟨s, S, he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩

theorem crtCall_two (v : CrtImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) (Two (At J2)) :=
  two_post (crt_ct v) fun _ _ ⟨s, S, he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (crt_call v (preF_of S.1) he hargs hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem pcArgs_two : RelCT isa (Two (At J2)) (.block pcArgs) (Two (At J3)) :=
  two_piece [.rsp] (pins_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (pcArgs_ok (preF_of S.1) he) fun _ ⟨he', _, hdi, hsi, hdx, hcx, h8, h9⟩ =>
      ⟨s, S, he', hdi, hsi, hdx, hcx, h8, h9⟩

theorem pcCall_two (pc : Prog isa) (name : String)
    (hok : ∀ s, pcContract.clear.pre s → ∃ t s', Exec isa pc s t s' ∧ abiPreserved s s' ∧ pcContract.post s s')
    (hct : ConstantTime isa pcContract.clear.pre pcContract.pub pc) (hsp : NoSp pc) (hd : pc.depth = 1) :
    RelCT isa (Two (At J3)) (.call name pc) (Two (At J4)) :=
  two_post (pc_ct pc name hok hct) fun _ _ ⟨s, S, he, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (pc_call pc name hok hsp hd (preF_of S.1) he hdi hsi hdx hcx h8 h9) fun _ ⟨he', hpc, _⟩ =>
      ⟨s, S, he', by
        cases hq : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) <;>
          simp only [hq] at hpc <;> simp only [preVal, hq] <;> exact hpc.2⟩

theorem pdArgs_two : RelCT isa (Two (At J4)) (.block pdArgs) (Two (At J5)) :=
  two_piece [.rsp] (pins_rsp fun _ _ h => h.1) (by taint_decide)
    fun _ t ⟨s, S, he, hpw⟩ => by
      have hp := preF_of S.1
      have hpwl := preWords_le hp
      refine WP.mono (pdArgs_ok hp he) fun t₃ ⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩ => ?_
      have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fb s) (8 * d) =
          [off (fb s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
        rw [hm₃]
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
        · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
          rfl
        · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
        · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
        · simp (disch := decide) only [word_writeW_self]; rfl
      have hpre : Spec.Rsa.wordsAt t₃.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
          Spec.Rsa.wordsAt t.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
        rw [hm₃]
        simp (disch := first | decide | (simp only [oPre, oR3]; omega)) only [words_wo, words_wo0]
      exact ⟨s, S, ⟨he₃, hpre.trans hpw⟩, hw (d := 0) (by decide), hw (d := 1) (by decide),
        hw (d := 2) (by decide), hw (d := 3) (by decide), hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩

theorem pdCall_two (P : PublicImpl) (name : String) :
    RelCT isa (Two (At J5)) (.call name (P.code)) (Two (At J2)) :=
  two_post (pd_ct P name) fun _ _ ⟨s, S, ⟨he, _⟩, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (pd_call P name (preF_of S.1) he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem cmpArgs_two : RelCT isa (Two (At J2)) (.block cmpArgs) (Two (At J7)) :=
  two_piece [.rsp] (pins_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (cmpArgs_ok (preF_of S.1) he) fun _ ⟨_, _, hdi, hsi, hcx, h10, _, k⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hsi, hcx, h10⟩

theorem tail_eq : seqs PrivChecked.tail =
    .seq (.block cmpArgs) (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) :=
  rfl

/-- The comparison and the release, from the registers `cmpArgs` sets. -/
theorem rest_ct : RelCT isa (Two (At J7))
    (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) fun _ _ => True :=
  two_taint [.rdi, .rsi, .rcx, .r10, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => stackArg s 0) (fun _ _ h => h.2.2.1) (fun _ _ S => S.arg (by decide)) h₁ h₂
    · exact pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2.2) (fun _ _ _ => rfl) h₁ h₂
    · exact pin fb (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂) (by taint_decide)

theorem body_ct (v : CrtImpl) (pcName pdName : String) :
    RelCT isa (Two (At J0)) (body v.name v.code pcName v.pc pdName
      (v.pubOp.code)) fun _ _ => True := by
  rw [body_eq, check_eq, tail_eq]
  exact RelCT.seq crtArgs_two (RelCT.seq (crtCall_two v) (RelCT.seq pcArgs_two
    (RelCT.seq (pcCall_two v.pc pcName v.pcOk v.pcCt v.pcNosp v.pcDepth) (RelCT.seq pdArgs_two
      (RelCT.seq (pdCall_two v.pubOp pdName) (RelCT.seq cmpArgs_two rest_ct))))))

/-! ## The frame -/

theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) : s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_push p₁
      obtain rfl := alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

theorem code_constantTime (v : CrtImpl) (pcName pdName : String) :
    ConstantTime isa chkContract.pre chkContract.pub (code v.name v.code pcName v.pc pdName
      (v.pubOp.code)) :=
  RelCT.constantTime (relCT_alloc ((body_ct v pcName pdName).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

/-- `vg_rsa_private_checked`, calling the implementation `v` of the CRT and
its independently verified public operation, meets the shared
contract. -/
theorem code_verified (v : CrtImpl) (pcName pdName : String) :
    Verified target (code v.name v.code pcName v.pc pdName
      (v.pubOp.code)) (Spec.Rsa.privateCheckedContract abi stackBytes) :=
  have hct : ConstantTime isa chkContract.pre chkContract.pub (code v.name v.code pcName
      v.pc pdName (v.pubOp.code)) := code_constantTime v pcName pdName
  Verified.of_correct (k := chkContract) (code_correct v pcName pdName) hct private_checked_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : CrtImpl) (pcName pdName : String) :
    (code v.name v.code pcName v.pc pdName (v.pubOp.code)).all
      (fun i => !isa.writesSp i) = true := by
  simp only [code, body_eq, check_eq, tail_eq, Code.all, v.spSafe, v.pcSpSafe, v.pubOp.spSafe,
    Bool.true_and]
  decide +kernel

end VG.Proof.Rsa.X86_64
