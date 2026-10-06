import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCTBase

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time, up to `D`

The first block, the private-key operation (constant time for its
contract, whose public data agree), and `D = I2OSP(d, k)`, whose loops
address `scratch` and `d` from pointers and lengths that are public.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- Callee-saved registers but `rsp` as on entry. -/
def CS (s t : State) : Prop := ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r

def J0 (s t : State) : Prop := t = allocState frameBytes s
def JS (s t : State) : Prop := Setup s t ∧ CS s t
def JP (s t : State) : Prop := PostPriv s t ∧ CS s t

theorem setup_two : RelCT isa (Two (At J0)) (.block setup) (Two (At JS)) :=
  two_blk [.rsp] (pins (J := J0) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t h; rw [h]; rfl)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp h => by
      subst h
      exact WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx, .r8, .r9] (setup_run hp) (by decide +kernel))
        fun t' ⟨h₁, k₁⟩ => ⟨h₁, fun r hr hr' => by
          rw [k₁.cs (by decide) r hr]; simp only [allocState_gpr, hr', ↓reduceIte]⟩


/-- A buffer the function only reads, as a callee from the frame sees it. -/
theorem entryBytes {s t : State} (hp : DPre s) (h : Setup s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hm : (mlR s).Disjoint ⟨p, len⟩)
    (hs : (⟨p, len⟩ : Region).Disjoint (scrR s)) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  have hk2 := hp.k2
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by decide)⟩) hk ho hm hs.symm hl

/-- What the private-key operation's contract makes public, from the entry state. -/
theorem priv_view {a s t : State} (S : Sib a s) (h : Setup s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (privRd s) (privWr s)).gpr =
      [a.gpr .rdi, a.gpr .r8, a.gpr .rcx, a.gpr .r8, a.gpr .r9, stackArg a 0, fb a - 8] ∧
    (List.range 14).map (stackArg (t.callEntry.withRegions (privRd s) (privWr s))) =
      ((List.range 14).map fun i => stackArg a (i + 3)) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (privRd s) (privWr s)).mem
      ((t.callEntry.withRegions (privRd s) (privWr s)).gpr .rdx)
      ((t.callEntry.withRegions (privRd s) (privWr s)).gpr .rcx).toNat = nB a ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (privRd s) (privWr s)).mem
      ((t.callEntry.withRegions (privRd s) (privWr s)).gpr .r8)
      ((t.callEntry.withRegions (privRd s) (privWr s)).gpr .r9).toNat = eB a := by
  have hp := S.p
  have hk2 := hp.k2
  have hsi := hp.hsi
  have g : ∀ {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions (privRd s) (privWr s)).gpr r = t.gpr r := fun hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [g (by decide), h.rdi, S.gpr (by decide), g (by decide), h.rsi, S.gpr (by decide), g (by decide), h.rdx,
      S.gpr (by decide), g (by decide), h.rcx, g (by decide), h.r8, S.gpr (by decide), g (by decide), h.r9,
      S.arg (by decide), State.withRegions_gpr, State.callEntry_rsp, h.rsp, S.fb, S.gpr (r := .r9) (by decide)]
  · refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    rw [priv_args h _ _ hi, S.arg (by omega)]
  · rw [g (by decide), g (by decide), h.rdx, h.rcx, entryBytes hp h _ _ hp.dKn
      (by have := hp.dOn; rw [outR]; exact this) hp.dMn hp.dns (by have := hp.wN; omega)]
    exact S.n
  · rw [g (by decide), g (by decide), h.r8, h.r9, entryBytes hp h _ _ hp.dKe
      (by have := hp.dOe; rw [outR]; exact this) hp.dMe hp.des (by have := hp.wE; omega)]
    exact S.e

theorem priv_ct (pv : PrivImpl) : RelCT isa (Two (At JS)) (.call pv.name pv.code) fun _ _ => True := by
  refine RelCT.callEx (k := privK) pv.ok pv.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁, _⟩, ⟨s₂, S₂, j₂, _⟩⟩ => ?_
  obtain ⟨r₁, a₁, n₁, e₁⟩ := priv_view S₁ j₁
  obtain ⟨r₂, a₂, n₂, e₂⟩ := priv_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := priv_covers S₁.p j₁
  obtain ⟨c₂, w₂⟩ := priv_covers S₂.p j₂
  exact ⟨privRd s₁, privWr s₁, privRd s₂, privWr s₂, priv_pre S₁.p j₁, priv_pre S₂.p j₂,
    ⟨List.map_inj_left.mp (r₁.trans r₂.symm), a₁.trans a₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.rsp, j₂.rsp, S₁.fb, S₂.fb]⟩

theorem priv_two (pv : PrivImpl) : RelCT isa (Two (At JS)) (.call pv.name pv.code) (Two (At JP)) :=
  two_then (priv_ct pv) fun _ _ hp ⟨h, hcs⟩ => WP.mono (priv_call pv hp h) fun _ ⟨hpost, hcs', _⟩ =>
    ⟨hpost, fun r hr hr' => (hcs' r hr).trans (hcs r hr hr')⟩


/-! ## `D` -/

def J1 (s t : State) : Prop := ∃ R EM, P1 s R EM t
def J2 (s t : State) : Prop := ∃ R EM t₀, P1 s R EM t₀ ∧ ZInv s t₀ (kOf s) t
def J3 (s t : State) : Prop := ∃ R EM t₀, P2 s R EM t₀ t
def JDB (s t : State) : Prop := ∃ R EM, DB s R EM t

theorem dBuild_ct : RelCT isa (Two (At JP)) dBuild fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := J1) [.rsp] (pins (J := JP) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t h; exact h.1.rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨h, hcs⟩ => WP.mono (p1_step hp h hcs) fun _ h' => ⟨_, _, h'⟩) ?_
  refine RelCT.seq (two_blk (J' := J2) [.rsp, .rdi, .rcx, .r10] (pins (J := J1) [(.rsp, fb), (.rdi, sc),
      (.rcx, fun s => s.gpr .r8), (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) s t ⟨_, _, h⟩
        · exact h.ctx.rsp
        · exact h.rdi
        · exact h.rcx
        · exact h.r10) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact sc_pin
        · exact gpr_pin (by decide)
        · exact const_pin _)) (by taint_decide)
    fun s t hp ⟨_, _, h⟩ => WP.mono (zeroLoop_ok hp h) fun _ h' => ⟨_, _, _, h, h'⟩) ?_
  refine RelCT.seq (two_blk (J' := J3) [.rsp] (pins (J := J2) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t ⟨_, _, _, h₀, h⟩
      exact (h.keep.gpr (by decide)).trans h₀.ctx.rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨_, _, _, h₀, h⟩ => WP.mono (p2_step hp h₀ h) fun _ h' => ⟨_, _, _, h'⟩) ?_
  exact two_taint [.rsp, .rsi, .rcx, .rdi, .r10] (pins (J := J3) [(.rsp, fb), (.rsi, fun s => stackArg s 1),
      (.rcx, fun s => stackArg s 2), (.rdi, fun s => off (sc s) (kOf s - dlOf s)),
      (.r10, fun _ => BitVec.ofNat 64 0)] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl) s t ⟨_, _, _, h⟩
        · exact h.ctx.rsp
        · exact h.rsi
        · exact h.rcx
        · exact h.rdi
        · exact h.r10) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl)
        · exact fb_pin
        · exact arg_pin (by decide)
        · exact arg_pin (by decide)
        · intro a s S; dsimp only; rw [S.scr, S.k, show dlOf s = dlOf a by simp only [dlOf, S.arg (i := 2) (by decide)]]
        · exact const_pin _)) (by taint_decide)

theorem dBuild_two : RelCT isa (Two (At JP)) dBuild (Two (At JDB)) :=
  two_then dBuild_ct fun _ _ hp ⟨h, hcs⟩ => WP.mono (dBuild_step hp h hcs) fun _ h' => ⟨_, _, h'⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
