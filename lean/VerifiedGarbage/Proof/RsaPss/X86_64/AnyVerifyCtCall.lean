module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCall
meta import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCtBase
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtCall
meta import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCall
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: the public-key operation in two runs

After the checks (`J7A`), `DB`'s slots and the precomputed public-key
operation's arguments (`dbPub_ctA`), and the call (`call_ctA`): its
arguments are public in both runs (the modulus, the exponent, the cached
values and their lengths, `EM`'s place and the working space), and it is
constant time by its contract.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {G : Spec.Mgf1.Hash} {H : Hash} {k g : Nat}

/-- The public words after the checks. -/
def K5A : List Nat := [15, 17, 18, 19, 20, 21, 22, 25, 26, 35, 36, 37, 38, 47, 48]

/-- And with `DB`'s. -/
def KMA : List Nat := [15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 35, 36, 37, 38, 47, 48]

theorem km_k5A {k : Nat} (h : k ∈ KMA) (h23 : k ≠ 23) (h24 : k ≠ 24) : k ∈ K5A := by
  simp only [KMA, K5A, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega

theorem km_ltA {k : Nat} (h : k ∈ KMA) : k < nW := by
  simp only [KMA, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega

variable (H) in
/-- After the checks: the salt's length fits, `rax = emLen - hLen - 2`. -/
def J7A (s t : State) : Prop :=
  VSA H s t K5A [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrRA s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (veml s - (H.D + 2)) ∧
    t.cf = some (decide (veml s - (H.D + 2) < (vrdxA s).toNat)) ∧ H.D + 2 ≤ veml s

variable (H) in
/-- Before the call. -/
def JC1A (s t : State) : Prop :=
  VSA H s t KMA [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrRA s) s.mem t.mem ∧
    (∀ i < 4, word t.mem (fb s) (8 * i) = vArgA s i) ∧ t.gpr .rdi = off (stackArg s 4) oEm ∧
    t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .r9 = s.gpr .rcx ∧ H.D + 2 ≤ veml s

variable (H) in
/-- After the call: the frame, the public words, what else `X` says. -/
def JMA (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  VSA H s t KMA [] (X s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- The modulus and the exponent, at the call, as on entry. -/
theorem entry_bytesA {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (vwrRA s) s.mem t.mem)
    {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrRA s)) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrRA s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
  exact bytesAt_frame fSE (vin_apartA hK hS) hl

theorem vArg_sibA {a s : State} (S : VSibA G k g a s) {i : Nat} : vArgA s i = vArgA a i := by
  unfold vArgA
  split <;> simp only [S.arg0, S.gpr (r := .rsi) (by decide), S.arg4, S.arg5]

theorem entry_eA {a s t : State} (S : VSibA G k g a s) (hst : t.gpr .rsp = fb s) (hM : Frame (vwrRA s) s.mem t.mem) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  have hp := S.ps
  rw [← S.eB]
  exact entry_bytesA (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKe hp.des
    (by have := hp.wE; dsimp only; omega)

variable (H) in
/-- Before the call. -/
def JCA (s t : State) : Prop :=
  VSA H s t KMA [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrRA s) s.mem t.mem ∧
    (∀ i < 4, word t.mem (fb s) (8 * i) = vArgA s i) ∧ t.gpr .rdi = off (stackArg s 4) oEm ∧
    t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 6 ∧ t.gpr .rcx = stackArg s 7 ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .r9 = s.gpr .rcx ∧ H.D + 2 ≤ veml s

theorem dbPub_ctA : RelCT isa (Two fun a t => VAtA G k g (J7A H) a t ∧ isa.eval .b t = some false)
    (.seq (.block dbSlots) (.block AnyHash.pubArgs)) (Two (VAtA G k g (JCA H))) := by
  refine two_post (vtwoA (G := G) (H := H) [17, 18, 19, 20, 21, 22, 26, 38] [.rax]
    (fun a => [(.rax, BitVec.ofNat 64 (veml a - (H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (fun k hk => by
      simp only [K5A, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega) _ (fun p hp => by
        rw [List.mem_singleton.mp hp, ← S.veml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) (by taint_decide)) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, hax, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have L := v.L
  have w : ∀ k ∈ K5A, W k = vwA H s k := hw
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R (w 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hM1 := vframe_keepA hp v.wr L.rsp hM f1
  have g1 : ∀ j, j ≠ 23 → j ≠ 24 → upd (upd W 24 (BitVec.ofNat 64 (veml s - (H.D + 2) + 1))) 23
      (off (stackArg s 4) (oEm + vlo s)) j = W j := fun j h23 h24 => by simp [upd, h23, h24]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (args_okA hp L1 R1 (k1.2.2.trans v.wr) (k1.2.1.trans hrd) hM1 (by rw [g1 17 (by decide) (by decide)]; exact w 17 (by decide))
      (by rw [g1 18 (by decide) (by decide)]; exact w 18 (by decide))
      (by rw [g1 19 (by decide) (by decide)]; exact w 19 (by decide))
      (by rw [g1 20 (by decide) (by decide)]; exact w 20 (by decide))
      (by rw [g1 22 (by decide) (by decide)]; exact w 22 (by decide))
      (by rw [g1 38 (by decide) (by decide)]; exact w 38 (by decide))))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ => ?_
  have hw1 : u1.wr = frR s :: s.wr := k1.2.2.trans v.wr
  refine ⟨s, S, ⟨L2, k2.2.2.trans hw1, ⟨V, W2, R2, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩,
    (k2.2.1.trans k1.2.1).trans hrd, vframe_keepA hp hw1 L1.rsp hM1 f2,
    fun i hi => (R2.fr i (by unfold nW frameBytes; omega)).trans (hW2a i hi), h2di, h2si, h2dx, h2cx, h2r8, h2r9,
    hok⟩
  have h4 : 4 ≤ k := by simp only [KMA, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  rw [hW2b k (km_ltA hk) h4]
  by_cases h23 : k = 23
  · subst h23; simp [upd, vwA]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, vwA, vdb]
    congr 1; omega
  rw [g1 k h23 h24]; exact w k (km_k5A hk h23 h24)

theorem entry_preA {a s t : State} (S : VSibA G k g a s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (vwrRA s) s.mem t.mem) :
    Spec.Rsa.wordsAt t.callEntry.mem (stackArg s 6) (stackArg s 7).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrRA s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
  exact (pre_wordsA S.ps fSE).trans S.preW

theorem call_pubA {a s₁ s₂ t₁ t₂ : State} (S₁ : VSibA G k g a s₁) (h₁ : JCA H s₁ t₁) (S₂ : VSibA G k g a s₂)
    (h₂ : JCA H s₂ t₂) :
    pdChkContract.pub (t₁.callEntry.withRegions (callRdA s₁) (vWrA s₁)) (t₂.callEntry.withRegions (callRdA s₂) (vWrA s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, -⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, -⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 4, stackArg (t₁.callEntry.withRegions (callRdA s₁) (vWrA s₁)) i = vArgA a i :=
    fun i hi => ((vstackArg_callA p₁ v₁.L.rsp _ _ hi).trans (ha₁ i hi)).trans (vArg_sibA S₁)
  have hE₂ : ∀ i < 4, stackArg (t₂.callEntry.withRegions (callRdA s₂) (vWrA s₂)) i = vArgA a i :=
    fun i hi => ((vstackArg_callA p₂ v₂.L.rsp _ _ hi).trans (ha₂ i hi)).trans (vArg_sibA S₂)
  have bn₁ := entry_preA S₁ v₁.L.rsp hM₁
  have bn₂ := entry_preA S₂ v₂.L.rsp hM₂
  have be₁ := entry_eA S₁ v₁.L.rsp hM₁
  have be₂ := entry_eA S₂ v₂.L.rsp hM₂
  rw [show pdChkContract.pub = pdContract.pub from rfl]
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, by rw [hE₁ 0 (by decide), hE₂ 0 (by decide)], by rw [hE₁ 1 (by decide), hE₂ 1 (by decide)],
    by rw [hE₁ 2 (by decide), hE₂ 2 (by decide)], by rw [hE₁ 3 (by decide), hE₂ 3 (by decide)], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.arg4, S₂.arg4]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rsi) (by decide),
        S₂.gpr (r := .rsi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.arg6, S₂.arg6]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.arg7, S₂.arg7]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn₁, bn₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be₁, be₂]

theorem call_ctA (impl : PublicImpl) : RelCT isa (Two (VAtA G k g (JCA H))) (.call impl.name impl.code) (Two (VAtA G k g (JMA H fun _ _ _ => True))) := by
  refine two_post (RelCT.callEx (k := pdChkContract) impl.ok impl.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨c₁, w₁⟩ := call_coversA S₁.ps h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := call_coversA S₂.ps h₂.2.1 h₂.1.wr
    exact ⟨_, _, _, _, call_preA S₁.ps h₁.1.L.rsp h₁.2.2.2.1 h₁.2.2.2.2.1 h₁.2.2.2.2.2.1 h₁.2.2.2.2.2.2.1
      h₁.2.2.2.2.2.2.2.1 h₁.2.2.2.2.2.2.2.2.1 h₁.2.2.2.2.2.2.2.2.2.1,
      call_preA S₂.ps h₂.1.L.rsp h₂.2.2.2.1 h₂.2.2.2.2.1 h₂.2.2.2.2.2.1 h₂.2.2.2.2.2.2.1
      h₂.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2.2.2.1, call_pubA S₁ h₁ S₂ h₂, c₁, w₁, c₂, w₂,
      by rw [h₁.1.L.rsp, h₂.1.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    have hk2 := hp.k2
    refine WP.mono (call_okA impl hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, _, hk', _⟩ => ?_
    have hEm : oEm + (s.gpr .rsi).toNat ≤ oRsa := by unfold oEm oRsa; omega
    have R' := R.of_em v.L.geo hEm hk'
    exact ⟨s, S, ⟨v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr', wr'.trans v.wr, ⟨_, W, R', hw, trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, hok⟩


end VG.Proof.RsaPss.X86_64.Any
