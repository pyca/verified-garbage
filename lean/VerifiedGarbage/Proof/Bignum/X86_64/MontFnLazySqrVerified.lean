module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazySqr
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazySqr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # `vg_rsa_lazy_mont_sqr_adx` meets `sqrLazyContract` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Spec.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)
open VG.Proof.MlKem.X86_64

/-- `vg_rsa_lazy_mont_sqr(ws = rdi, ws_len = rsi, o = edx, a = ecx, k = r8d)`. -/
def fnSqrContract : Contract isa where
  pre s :=
    let ws := s.gpr .rdi
    let n := (s.gpr .rsi).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨ws, n * 8⟩ ∧
      ws.toNat + n * 8 ≤ 2 ^ 64 ∧ Layout s.mem ws n ∧ Operand (idx s .rdx) ∧ idx s .rdx ≠ aM ∧
      Operand (idx s .rcx) ∧ 1 ≤ idx s .r8 ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat * (wordAt s.mem ws minvWord).toNat + 1) %
        2 ^ 64 = 0
  post s s' :=
    let ws := s.gpr .rdi
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt s'.mem ws w (idx s .rdx) * (2 ^ (64 * w)) ^ (2 ^ idx s .r8 - 1) % M =
        numAt s.mem ws w (idx s .rcx) ^ 2 ^ idx s .r8 % M ∧
      Spec.Rsa.Mont.Keeps ws (s.gpr .rsi).toNat w (idx s .rdx) s.mem s'.mem
  pub := fnContract.pub

theorem fnSqr_implies : fnSqrContract.Implies (Spec.Rsa.Mont.sqrLazyContract abi) where
  pre := by sig_implies_pre [Spec.Rsa.Mont.sqrLazyContract, Spec.Rsa.Mont.sqrSig, fnSqrContract, abi, argRegs]
  post := by sig_implies_post [Spec.Rsa.Mont.sqrLazyContract, Spec.Rsa.Mont.sqrSig, fnSqrContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.Mont.sqrLazyContract, Spec.Rsa.Mont.sqrSig, fnSqrContract, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hsp, hdi, hsi, hdx, hcx, h8, List.singleton_inj.mp hw⟩
  sat := by
    sig_implies_sat [Spec.Rsa.Mont.sqrLazyContract, Spec.Rsa.Mont.sqrSig, fnSqrContract, abi, argRegs] [satState]
      using satState

/-- What `fnSqrContract.pre` gives the proofs: `fn_good`'s. -/
theorem fnSqr_good {s : State} (h : fnSqrContract.pre s) :
    Scr s (s.gpr .rdi) ((s.gpr .rsi).toNat * 8) ∧
    Hdr s.mem (s.gpr .rdi) (wOf s.mem (s.gpr .rdi)) (wordAt s.mem (s.gpr .rdi) minvWord) ∧
    slot (wOf s.mem (s.gpr .rdi)) 8 ≤ (s.gpr .rsi).toNat * 8 ∧ 2 ≤ wOf s.mem (s.gpr .rdi) ∧
    wOf s.mem (s.gpr .rdi) < 2 ^ 31 := by
  obtain ⟨-, hwr, -, hnw, ⟨h2, h31, h8, harr⟩, -⟩ := h
  refine ⟨Scr.of_mem (by rw [hwr]; simp) hnw, ⟨?_, rfl, fun j hj => harr j hj⟩, by
    simp only [slot, hdrBytes, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] at h8 ⊢; omega, h2, h31⟩
  simp [word, wOf, wordAt, Spec.Rsa.Mont.wWord, sW, off]

theorem fnSqrAdx_correct (s : State) (h : fnSqrContract.pre s) :
    ∃ t s', Exec isa sqrAdxLazy s t s' ∧ abiPreserved s s' ∧ fnSqrContract.post s s' := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fnSqr_good h
  obtain ⟨-, hwr, hret, hnw, -, ⟨ho, ho2, ho3⟩, ho0, ⟨ha, ha2, ha3⟩, hk1, hinv⟩ := h
  suffices hwp : WP isa sqrAdxLazy s fun s' => gprPreserved s s' ∧ fnSqrContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  refine WP.mono (sqrAdxLazy_ok hs rfl hH hZ hw hw' ho ha ho2 ho3 ho0 ha2 ha3 hk1 (by simp only [idx]; omega)
    (idx_eq s .rdx) (idx_eq s .rcx) (idx_eq s .r8) hinv) fun t ⟨heq, har, k, hcs⟩ => ?_
  have hn := hs.nowrap
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · exact k.gpr (by decide)
    all_goals exact hcs _ (by simp)
  · refine Mem.readW_congr fun i hi => har _ fun j hj => Or.inr ?_
    have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx
    have := slot_le (w := wOf s.mem (s.gpr .rdi)) (show j < 8 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> first | decide | omega)
    simp only [ofs]; omega
  · rw [numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'
    exact this

/-! ## Constant time -/

/-- The public data of a call: the working space, its size, `w`, the indices and `k`. -/
structure SqrData where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  a : Nat
  k : Nat

/-- What the call's precondition gives the loop, for the state `s` at the call. -/
def SqrConds (d : SqrData) (s : State) (minv : BitVec 64) : Prop :=
  slot d.w 8 ≤ d.Z ∧ 2 ≤ d.w ∧ d.w < 2 ^ 31 ∧ d.o < 8 ∧ d.a < 8 ∧ d.o ≠ aAcc ∧ d.o ≠ aTmp ∧ d.o ≠ aN ∧
    d.a ≠ aAcc ∧ d.a ≠ aTmp ∧ 1 ≤ d.k ∧ d.k < 2 ^ 32 ∧
    ((word s.mem d.B (slot d.w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0

/-- After `j` squarings of a call. -/
def SqrL (p : SqrData × Nat) (t : State) : Prop :=
  ∃ s minv, SqrConds p.1 s minv ∧ SqrInv s t p.1.B p.1.Z p.1.w minv p.1.o p.1.a p.1.k p.2

theorem SqrL.mid {p : SqrData × Nat} {t : State} (h : SqrL p t) :
    AdxMid ⟨p.1.B, p.1.Z, p.1.w, p.1.o, cur p.1.a p.1.o p.2, cur p.1.a p.1.o p.2⟩ t := by
  obtain ⟨s, minv, ⟨hZ, -, -, ho, ha, ho1, ho2, -, ha1, ha2, -⟩, I⟩ := h
  have hc : cur p.1.a p.1.o p.2 < 8 := by unfold cur; split <;> assumption
  have hc1 : cur p.1.a p.1.o p.2 ≠ aAcc := by unfold cur; split <;> assumption
  have hc2 : cur p.1.a p.1.o p.2 ≠ aTmp := by unfold cur; split <;> assumption
  exact ⟨⟨I.scr, I.rdi, ⟨minv, I.hdr⟩, hZ, ⟨ho, hc, hc, ho1, ho2, hc1, hc2, hc1, hc2⟩, I.rdx, I.rcx, I.r8⟩, I.ops⟩

/-- A turn of the loop, for one run. -/
theorem sqrL_step {p : SqrData × Nat} {t : State} (h : SqrL p t) (hj : p.2 < p.1.k) :
    WP isa (.seq adxBodyLazy (.block sqrNextAdx)) t
      fun t' => t'.zf = some (decide (p.2 + 1 = p.1.k)) ∧ SqrL (p.1, p.2 + 1) t' := by
  obtain ⟨s, minv, hc, I⟩ := h
  obtain ⟨hZ, hw, hw', ho, ha, ho1, ho2, ho0, ha1, ha2, hk1, hk, hinv⟩ := hc
  exact WP.mono (sqrStep_ok I hj hk hZ hw hw' ho ha ho1 ho2 ho0 ha1 ha2 hinv) fun t ⟨hz, I', _⟩ =>
    ⟨hz, s, minv, ⟨hZ, hw, hw', ho, ha, ho1, ho2, ho0, ha1, ha2, hk1, hk, hinv⟩, I'⟩

/-- A turn of the loop, and its timing, from runs after the same number of squarings. -/
theorem sqrTurn_ct (p : SqrData × Nat) (hj : p.2 < p.1.k) :
    RelCT isa (fun s₁ s₂ => SqrL p s₁ ∧ SqrL p s₂) (.seq adxBodyLazy (.block sqrNextAdx))
      fun t₁ t₂ => (t₁.zf = some (decide (p.2 + 1 = p.1.k)) ∧ SqrL (p.1, p.2 + 1) t₁) ∧
        (t₂.zf = some (decide (p.2 + 1 = p.1.k)) ∧ SqrL (p.1, p.2 + 1) t₂) := by
  have core : RelCT isa (Two AdxMid) (.seq adxBodyLazy (.block sqrNextAdx)) fun _ _ => True :=
    RelCT.seq (RelCT.keepRdi (f := CallData.B) adxBodyLazy_ct (by rw [← Code.allInstrs_eq]; decide +kernel)
      fun _ _ h => h.1.2.1)
      (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))
  exact (RelCT.wp (core.mono (fun _ _ h => ⟨_, h.1.mid, h.2.mid⟩) fun _ _ h => h)
    fun s₁ s₂ h => ⟨sqrL_step h.1 hj, sqrL_step h.2 hj⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Runs with `n` squarings left. -/
def SqrLeft (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ p : SqrData × Nat, (n = p.1.k - p.2 ∧ p.2 < p.1.k ∧ SqrL p s₁) ∧ (n = p.1.k - p.2 ∧ p.2 < p.1.k ∧ SqrL p s₂)

/-- The loop, from runs after the same number of squarings, `n` of them left. -/
theorem sqrLoop_ct (n : Nat) :
    RelCT isa (SqrLeft n) (.loop (.seq adxBodyLazy (.block sqrNextAdx)) .ne)
      (Two fun (d : SqrData) t => SqrL (d, d.k) t) := by
  refine RelCT.loop (M := isa) SqrLeft (fun n => ?_) n
  refine RelCT.exists_ (M := isa) (P := fun (p : SqrData × Nat) (s₁ s₂ : State) =>
    (n = p.1.k - p.2 ∧ p.2 < p.1.k ∧ SqrL p s₁) ∧ (n = p.1.k - p.2 ∧ p.2 < p.1.k ∧ SqrL p s₂)) fun p => ?_
  by_cases hj : p.2 < p.1.k
  swap
  · exact RelCT.of_false fun _ _ h => hj h.1.2.1
  by_cases hn : n = p.1.k - p.2
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1.1
  refine (sqrTurn_ct p hj).mono (fun _ _ h => ⟨h.1.2.2, h.2.2.2⟩) fun t₁ t₂ ⟨⟨z₁, L₁⟩, ⟨z₂, L₂⟩⟩ => ?_
  refine ⟨by simp only [eval, z₁, z₂], fun he => ?_, fun he => ?_⟩
  · have e : p.2 + 1 = p.1.k := by
      by_contra c; simp [eval, z₁, c] at he
    rw [e] at L₁ L₂
    exact ⟨p.1, L₁, L₂⟩
  · have e : p.2 + 1 ≠ p.1.k := by
      intro c; simp [eval, z₁, c] at he
    exact ⟨p.1.k - (p.2 + 1), by omega, (p.1, p.2 + 1), ⟨rfl, by simp only; omega, L₁⟩, ⟨rfl, by simp only; omega, L₂⟩⟩

/-- A call's public data in the state at the call. -/
def FnPhiSqr (d : SqrData) (s : State) : Prop :=
  fnSqrContract.pre s ∧ s.gpr .rdi = d.B ∧ (s.gpr .rsi).toNat * 8 = d.Z ∧ wOf s.mem d.B = d.w ∧
    idx s .rdx = d.o ∧ idx s .rcx = d.a ∧ idx s .r8 = d.k

/-- After `zext`: the rest of the head runs to the loop, and the registers it
addresses with are public. -/
def SqrZ (d : SqrData) (t : State) : Prop :=
  WP isa (.block (sqrArgs ++ saves ++ slotsIn ++ sqrInit)) t (fun u => SqrL (d, 0) u) ∧ t.gpr .rdi = d.B ∧
    t.gpr .rdx = (BitVec.ofNat 32 d.o).setWidth 64 ∧ t.gpr .rcx = (BitVec.ofNat 32 d.a).setWidth 64 ∧
    t.gpr .r8 = (BitVec.ofNat 32 d.k).setWidth 64

theorem pins_sqrZ : Pins SqrZ [.rdi, .rdx, .rcx, .r8] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨-, a₂, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

theorem sqrHead_split : zext ++ sqrArgs ++ saves ++ slotsIn ++ sqrInit = zext ++ (sqrArgs ++ saves ++ slotsIn ++ sqrInit) := by
  simp only [List.append_assoc]

theorem fnSqrAdx_rel : RelCT isa (Two FnPhiSqr) sqrAdxLazy fun _ _ => True := by
  unfold sqrAdxLazy
  rw [sqrHead_split]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := SqrZ)
    (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)) fun d s h => ?_)
    (two_post (two_taint _ pins_sqrZ (by taint_decide)) fun _ _ h => h.1)))
    (RelCT.seq (RelCT.exists_ (M := isa) (P := fun (d : SqrData) (s₁ s₂ : State) => SqrL (d, 0) s₁ ∧ SqrL (d, 0) s₂)
      fun d => (sqrLoop_ct d.k).mono (fun s₁ s₂ h => ⟨(d, 0), ⟨(Nat.sub_zero _).symm, ?_, h.1⟩,
        ⟨(Nat.sub_zero _).symm, ?_, h.2⟩⟩) fun _ _ h => h)
      (two_taint [.rdi] (fun d _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        obtain ⟨_, _, _, I₁⟩ := h₁; obtain ⟨_, _, _, I₂⟩ := h₂; rw [I₁.rdi, I₂.rdi]) (by taint_decide)))
  · obtain ⟨hp, hdi, hZ, hw, ho, ha, hk⟩ := h
    obtain ⟨hs, hH, hZ8, hw2, hw31⟩ := fnSqr_good hp
    obtain ⟨-, -, -, -, -, ⟨ho8, ho2, ho3⟩, ho0, ⟨ha8, ha2, ha3⟩, hk1, hinv⟩ := hp
    have hk32 : idx s .r8 < 2 ^ 32 := by simp only [idx]; omega
    have hhead := sqrHead_ok hs rfl hH hZ8 ho8 ha8 hk32 (idx_eq s .rdx) (idx_eq s .rcx) (idx_eq s .r8)
    rw [sqrHead_split, WP.block_append_iff] at hhead
    refine WP.mono (wp_conj hhead (zext_ok s)) fun t ⟨hw', h1, h2, h3, h4⟩ => ⟨WP.mono hw' ?_, ?_, ?_, ?_, ?_⟩
    · rintro u ⟨I, -⟩
      obtain ⟨B, Z, w, o, a, k⟩ := d
      simp only at hdi hZ hw ho ha hk ⊢
      subst hdi hZ hw ho ha hk
      exact ⟨s, _, ⟨hZ8, hw2, hw31, ho8, ha8, ho2, ho3, ho0, ha2, ha3, hk1, hk32, hinv⟩, I⟩
    · rw [h1, hdi]
    · rw [h2, idx_eq s .rdx, ho]
    · rw [h3, idx_eq s .rcx, ha]
    · rw [h4, idx_eq s .r8, hk]
  · obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, -, -, hk1, -⟩, -⟩ := h.1; exact hk1
  · obtain ⟨_, _, ⟨-, -, -, -, -, -, -, -, -, -, hk1, -⟩, -⟩ := h.2; exact hk1

theorem fnSqrAdx_ct : ConstantTime isa fnSqrContract.pre fnSqrContract.pub sqrAdxLazy :=
  RelCT.constantTime (fnSqrAdx_rel.mono (fun s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hw⟩ =>
    ⟨⟨s₁.gpr .rdi, (s₁.gpr .rsi).toNat * 8, wOf s₁.mem (s₁.gpr .rdi), idx s₁ .rdx, idx s₁ .rcx, idx s₁ .r8⟩,
      ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h₂, hdi.symm, by rw [hsi], (congrArg (wOf s₂.mem) hdi).trans hw.symm, by simp only [idx, hdx],
        by simp only [idx, hcx], by simp only [idx, h8]⟩⟩) fun _ _ h => h)

/-- `vg_rsa_lazy_mont_sqr_adx` on x86-64. -/
theorem fnSqrAdx_verified : Verified target sqrAdxLazy (Spec.Rsa.Mont.sqrLazyContract abi) :=
  Verified.of_correct fnSqrAdx_correct fnSqrAdx_ct fnSqr_implies

end VG.Proof.Bignum.X86_64.MontFn
