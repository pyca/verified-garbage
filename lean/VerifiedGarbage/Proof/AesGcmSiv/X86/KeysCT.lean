import VerifiedGarbage.Proof.AesGcmSiv.X86.Open

/-!
# AES-GCM-SIV on x86: the keys are constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments (`Env p`) leak the same trace: the code between calls
by the taint analysis, from `ebp` and the registers holding pointers or
counts that the correctness proofs pin to public values (a pointer loaded
from a slot in the block that uses it is pinned after its load: `ldPin`);
each call by its callee's proof (`callCtr_ct`, `callKey_ct`); and a loop
with calls by its iterations, each from the public number of iterations
left (`CT.loopN`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl)

/-- A loop of `n` iterations, its body constant time and leaving the
condition to loop back exactly while iterations are left. -/
theorem CT.loopN {body : Prog isa} {c : Cond} (Inv : Nat → State → Prop)
    (hb : ∀ n, CT (Inv n) body)
    (hw : ∀ n s, Inv n s → WP isa body s fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s'))
    (n : Nat) : CT (Inv n) (.loop body c) := by
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) (fun n (s₁ s₂ : State) => Inv n s₁ ∧ Inv n s₂) (fun n => ?_) n
  have h := RelCT.wp (hb n) (F₁ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) (F₂ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) fun s₁ s₂ h => ⟨hw n s₁ h.1, hw n s₂ h.2⟩
  refine RelCT.mono h (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨hn, c₁, i₁⟩, ⟨_, c₂, i₂⟩⟩ => ⟨by rw [c₁, c₂], fun _ => trivial,
    fun ht => ?_⟩
  rw [c₁] at ht
  have h1 : n ≠ 1 := by simpa using ht
  exact ⟨n - 1, by omega, i₁ h1, i₂ h1⟩

theorem CT.of_empty {I : State → Prop} {c : Prog isa} (h : ∀ s, ¬ I s) : CT I c :=
  RelCT.of_false fun s₁ _ hp => h s₁ hp.1

/-- A block that loads a register `r` from the slot `o` first, then uses it
(as an address): the rest is constant time from `ebp` and `r`, which holds
the public value `x` the slot holds. -/
theorem ldPin {I : State → Prop} {r : Reg} {o : Nat} {x : BitVec 32} {is : List Instr} {W : BitVec 32}
    (hW : ∀ s, I s → s.gpr .ebp = W ∧ slotv s.mem W o = x ∧ InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4)
    (hwW : W.toNat + o + 4 ≤ 2 ^ 32) (hr : r ≠ .ebp)
    {hc₁ : Taint.Hint VG.X86.taint.T}
    (h₁ : (VG.X86.taint.check (τr [.ebp]) (.block [.mov r (slot o)]) hc₁).isSome = true)
    {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr [.ebp, r]) (.block is) hc).isSome = true) :
    CT I (.block (.mov r (slot o) :: is)) := by
  have e : (.mov r (slot o) :: is : List Instr) = [.mov r (slot o)] ++ is := rfl
  rw [e]
  refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧ s.gpr r = x)
    (CT.taint [.ebp] (pin_ebp fun s h => (hW s h).1) h₁) (fun s hs => ?_)
    (CT.taint [.ebp, r] (pin2 fun _ h => h) h))
  obtain ⟨bp, sl, ir⟩ := hW s hs
  have aW : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := Proof.AesGcm.X86.w64_add (by omega)
  simp only [slotv_eq] at sl
  have hr' : Reg.ebp ≠ r := fun h => hr h.symm
  refine WP.of_runBlock ⟨_, by grun [bp, aW, ir], ?_, ?_⟩
  · rw [VG.X86.RegUpd.gpr_setReg_of_ne _ _ hr', bp]
  · gregs [sl]

/-! ## `derive` -/

theorem deriveBlock_ct {p : Prm} (L : Lay p) {I : State → Prop} (hI : ∀ s, I s → Env p s) :
    CT I (.block deriveBlock) :=
  ldPin (r := .eax) (o := nonceO) (x := p.N) (W := p.W)
    (fun s h => ⟨(hI s h).ebp, (hI s h).slots.nonce, (hI s h).perm.wR (by decide)⟩) (by have := L.ww; unfold nonceO; omega)
    (by decide) (by taint_decide) (by taint_decide)

theorem derivePost_ct {p : Prm} (L : Lay p) {I : State → Prop} {i : Nat}
    (hI : ∀ s, I s → Env p s ∧ slotv s.mem p.W iO = BitVec.ofNat 32 i) : CT I (.block derivePost) :=
  ldPin (r := .edx) (o := iO) (x := BitVec.ofNat 32 i) (W := p.W)
    (fun s h => ⟨(hI s h).1.ebp, (hI s h).2, (hI s h).1.perm.wR (by decide)⟩) (by have := L.ww; unfold iO; omega)
    (by decide) (by taint_decide) (by taint_decide)

/-- The state of a step of `derive` before its call. -/
structure DerCall (p : Prm) (i : Nat) (t₁ : State) : Prop where
  env : Env p t₁
  key : KeyOk p t₁ p.K
  dst : Dst p t₁ p.K (p.W + BitVec.ofNat 32 224) (16 * 1)
  eax : t₁.gpr .eax = p.K
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.W + BitVec.ofNat 32 224
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  ix : slotv t₁.mem p.W iO = BitVec.ofNat 32 i

theorem derCall_of {p : Prm} (L : Lay p) {σ t t₁ : State} {i : Nat} (I : DInv p σ i t)
    (run : runBlock isa deriveBlock t = some t₁) : DerCall p i t₁ := by
  obtain ⟨u₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, -, rd₁, wr₁⟩ := derArgs_ok L I.env I.ix
  have e : u₁ = t₁ := Option.some.inj (run₁.symm.trans run)
  subst e
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem u₁.mem := by
    rw [hm₁]; exact derMem_frame _ _ _ _
  have E₁ : Env p u₁ := I.env.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  refine ⟨E₁, keyK L E₁.perm, dstW L E₁.perm (q := 224) (.inr ⟨by decide, by decide⟩) (L.k_w' (by decide)), eax,
    ecx, edx, ebx, edi, ?_⟩
  rw [← I.ix]
  exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)

/-- A step of `derive`. -/
theorem derStep_ct (v : GcmImpl) {p : Prm} (L : Lay p) {i : Nat} :
    CT (fun s => ∃ σ, DInv p σ i s) (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) := by
  refine CT.seq (J := DerCall p i) (deriveBlock_ct L fun s ⟨_, I⟩ => I.env) (fun t ⟨σ, I⟩ => by
      obtain ⟨t₁, run₁, -⟩ := derArgs_ok L I.env I.ix
      exact WP.of_runBlock ⟨t₁, run₁, derCall_of L I run₁⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ slotv s.mem p.W iO = BitVec.ofNat 32 i)
    (callCtr_ct v L (Q := p.K) (D := p.W + BitVec.ofNat 32 224) (n := 1) fun t₁ C =>
      ⟨C.env, C.key, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)
    (fun t₁ C => WP.mono (callCtr_ok v L C.env C.key C.dst
      (by rw [L.aW (by decide)]; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))) C.eax C.ecx C.edx C.ebx
      C.edi) fun s P => ⟨P.env, ?_⟩) (derivePost_ct L fun _ h => h)
  rw [← C.ix]
  exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm) (by decide)

theorem derive_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (derive v.callees) := by
  have hR := L.rounds
  have hk : 1 ≤ p.R / 2 - 1 := by rcases hR with h | h <;> rw [h] <;> decide
  refine CT.seq (J := fun s => ∃ σ, DInv p σ 0 s) (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide))
    (fun σ E => by obtain ⟨t₀, run₀, I₀⟩ := derive0_ok L E; exact WP.of_runBlock ⟨t₀, run₀, σ, I₀⟩) ?_
  refine (CT.loopN (fun k s => ∃ σ i, k = p.R / 2 - 1 - i ∧ i < p.R / 2 - 1 ∧ DInv p σ i s) (fun k => ?_)
    (fun k s ⟨σ, i, hk', hi, I⟩ => ?_) (p.R / 2 - 1)).mono fun s ⟨σ, I⟩ => ⟨σ, 0, by omega, by omega, I⟩
  · by_cases hkk : 0 < k ∧ k ≤ p.R / 2 - 1
    · exact (derStep_ct v L (i := p.R / 2 - 1 - k)).mono fun s ⟨σ, i, hk', hi, I⟩ => ⟨σ, by
        rw [show p.R / 2 - 1 - k = i by omega]; exact I⟩
    · exact CT.of_empty fun s ⟨σ, i, hk', hi, _⟩ => hkk ⟨by omega, by omega⟩
  · refine WP.mono (derStep_ok v L hi I) fun s' ⟨I', hz⟩ => ⟨by omega, by rw [eval_ne hz]; simp; omega,
      fun hk1 => ⟨σ, i + 1, by omega, by omega, I'⟩⟩

/-! ## `expand` and `hkey` -/

theorem expand_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (expand v.callees) := by
  refine CT.seq (J := fun t₁ => Env p t₁ ∧ t₁.gpr .eax = p.W + BitVec.ofNat 32 32 ∧
      t₁.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R) ∧ t₁.gpr .edx = p.W + BitVec.ofNat 32 512)
    (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)) (fun s E => ?_) (callKey_ct v L fun _ h => h)
  obtain ⟨t₁, run₁, eax, ecx, edx, bp, sp, _, rd, wr, hm⟩ := expArgs_ok L E
  exact WP.of_runBlock ⟨t₁, run₁, E.keep (by rw [bp, E.ebp]) (by rw [sp, E.esp]) rd wr hm, eax, ecx, edx⟩

theorem keys_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (keys v.callees) :=
  CT.seq (derive_ct v L) (fun s E => WP.mono (derive_ok v L E) fun _ I => I.env)
    (CT.seq (expand_ct v L) (fun s E => WP.mono (expand_ok v L E) fun _ X => X.env)
      (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)))

end VG.Proof.AesGcmSiv.X86
