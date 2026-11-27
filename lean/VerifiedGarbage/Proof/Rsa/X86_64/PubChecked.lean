module

import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCode
public import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.X86_64.Checked
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.X86_64.Checked
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Rsa.X86_64.Guarded`, which this module and modules that import it used -/

section

/-!
# RSA on x86-64: a function guarded by the check of its public exponent

`guarded c` runs `expCheck`, then `failOut` if `e` is not within
BoringSSL's limits and `c` if it is. `expCheck` changes only `rax`, `r10`,
`r11` and the flags, so `c` runs from a state that agrees with the entry
state on its arguments, memory and permissions (`Same`): for a contract `k`
of `c` that depends only on those, `guarded c` is correct
(`guarded_correct`) and constant time (`guarded_ct`) whenever `c` is.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- `t` agrees with `s` on the argument registers, `rsp`, memory and
permissions. -/
structure Same (s t : State) : Prop where
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rsi
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = s.gpr .rcx
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9
  rsp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Same.of_keep {s t : State} (k : Keep [.rax, .r10, .r11] s t) (hm : t.mem = s.mem) : Same s t :=
  ⟨k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), k.gpr (by decide),
    k.gpr (by decide), k.gpr (by decide), hm, k.2.1, k.2.2⟩

/-- The public exponent: the `r9` bytes at `r8`. -/
def eBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

/-- Whether the public exponent is within BoringSSL's limits. -/
def eValid (s : State) : Bool := Spec.Rsa.exponentValid (Spec.Rsa.os2ip (eBytes s))

/-- What `guarded` needs of a state its contract allows: `out` (`rdi`) of
`out_len` (`rsi`) bytes, writable, not holding the return address; `e`
(`r8`) of `e_len` (`r9`) bytes, readable. -/
structure Geom (s : State) : Prop where
  k1 : 1 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat < 2 ^ 63
  out : ∀ j < (s.gpr .rsi).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  ret : ∀ b < 8, ∀ j < (s.gpr .rsi).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat < 2 ^ 63
  e : ∀ i < (s.gpr .r9).toNat, InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 i) 1

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem eValid_same {s t : State} (h : Same s t) : eValid t = eValid s := by
  simp only [eValid, eBytes, h.mem, h.r8, h.r9]

/-- `expCheck`, from the entry state. -/
theorem expCheck_entry {s : State} (g : Geom s) :
    WP isa expCheck s fun t => t.zf = some (eValid s) ∧ Same s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide +kernel) (expCheck_ok rfl (ofNat_toNat _).symm g.L1 g.L2 g.e rfl)
    fun t ⟨hz, hm, k⟩ hmx => ⟨hz, Same.of_keep k hm, fun r hr => k.gpr (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hmx⟩

/-- `guarded c` is correct if `c` is for a valid `e`, from states agreeing
with the entry state (`hpre`): with `c`'s postcondition if `e` is valid
(`hok`), with zeros and 0 if not (`hfail`). -/
theorem guarded_correct {c : Prog isa} {k : Contract isa} {post : State → State → Prop}
    (hc : ∀ s, k.pre s → eValid s = true → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hgeom : ∀ s, k.pre s → Geom s) (hpre : ∀ s t, Same s t → k.pre s → k.pre t)
    (hok : ∀ s t s', k.pre s → Same s t → eValid s = true → k.post t s' → post s s')
    (hfail : ∀ s s', k.pre s → eValid s = false →
      Spec.Rsa.bytesAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0 →
      s'.gpr .rax = 0 → post s s')
    (s : State) (h : k.pre s) : ∃ t s', Exec isa (guarded c) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  have g := hgeom s h
  refine WP.seq (WP.mono (expCheck_entry g) fun t ⟨hz, hs, hcs, hmx⟩ => ?_)
  refine WP.ite (!eValid s) (by simp [eval, hz]) (fun hb => ?_) (fun hb => ?_)
  · have hv : eValid s = false := by simpa using hb
    refine WP.mono_mx (by decide +kernel) (failOut_ok (s := t) (op := s.gpr .rdi) (k := (s.gpr .rsi).toNat)
      hs.rdi (by rw [hs.rsi, ofNat_toNat]) g.k1 g.k2 (fun j hj => by rw [hs.wr]; exact g.out j hj))
      fun s' ⟨hb', hax, hfr, k'⟩ hmx' => ⟨⟨fun r hr => ?_, ?_, by rw [hmx', hmx]⟩, hfail s s' h hv hb' hax⟩
    · rw [k'.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hcs r hr]
    · refine Mem.readW_congr fun b hb => ?_
      rw [hfr _ fun j hj => g.ret b hb j hj, hs.mem]
  · have hv : eValid s = true := by simpa using hb
    obtain ⟨tr, s', he, habi, hp⟩ := hc t (hpre s t hs h) (by rw [← hv]; exact eValid_same hs)
    refine ⟨tr, s', he, ⟨fun r hr => (habi.1 r hr).trans (hcs r hr), ?_, ?_⟩, hok s t s' h hs hv hp⟩
    · rw [← hs.rsp, ← hs.mem]; exact habi.2.1
    · rw [habi.2.2, hmx]

/-- Two runs of `c` from states its contract allows and agreeing on its
public data leak the same. -/
theorem relCT_of_ct {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (h : ConstantTime isa pre pub c) :
    RelCT isa (fun s₁ s₂ => pre s₁ ∧ pre s₂ ∧ pub s₁ s₂) c fun _ _ => True :=
  fun _ _ _ _ _ _ ⟨p₁, p₂, hp⟩ e₁ e₂ => ⟨h _ _ _ _ _ _ p₁ p₂ hp e₁ e₂, trivial⟩

/-- `guarded c` is constant time if `c` is for a valid `e`: `expCheck` and
`failOut` by the taint analysis, from the pointers and lengths, and the
branch on public data. -/
theorem guarded_ct {c : Prog isa} {k : Contract isa}
    (hct : ConstantTime isa (fun s => k.pre s ∧ eValid s = true) k.pub c)
    (hgeom : ∀ s, k.pre s → Geom s) (hpre : ∀ s t, Same s t → k.pre s → k.pre t)
    (hpub : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ →
      (∀ r ∈ [Reg.rdi, .rsi, .r8, .r9], s₁.gpr r = s₂.gpr r) ∧ eBytes s₁ = eBytes s₂)
    (hpubS : ∀ s₁ s₂ t₁ t₂, Same s₁ t₁ → Same s₂ t₂ → k.pub s₁ s₂ → k.pub t₁ t₂) :
    ConstantTime isa k.pre k.pub (guarded c) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hexp := (RelCT.taint (A := taint) (Taint.ofRegs [.r8, .r9])
    (P := fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂)
    (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => Taint.agree_ofRegs fun r hr => (hpub _ _ p₁ p₂ hp).1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by taint_decide)).wpDep
    (F := fun (s t : State) => t.zf = some (eValid s) ∧ Same s t)
    fun s₁ s₂ ⟨p₁, p₂, _⟩ => ⟨WP.mono (expCheck_entry (hgeom _ p₁)) fun _ h => ⟨h.1, h.2.1⟩,
      WP.mono (expCheck_entry (hgeom _ p₂)) fun _ h => ⟨h.1, h.2.1⟩⟩
  refine RelCT.seq hexp (RelCT.ite ?_ ?_ ?_)
  · rintro u₁ u₂ ⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨z₁, -⟩, ⟨z₂, -⟩⟩
    simp only [eval, z₁, z₂, eValid, (hpub _ _ p₁ p₂ hp).2]
  · refine (RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi]) (fun u₁ u₂ hu => ?_) (by taint_decide)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, s₁⟩, ⟨-, s₂⟩⟩, -⟩ := hu
    have hr := (hpub _ _ p₁ p₂ hp).1
    refine Taint.agree_ofRegs fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · rw [s₁.rdi, s₂.rdi]; exact hr _ (by simp)
    · rw [s₁.rsi, s₂.rsi]; exact hr _ (by simp)
  · refine (relCT_of_ct hct).mono (fun u₁ u₂ hu => ?_) fun _ _ _ => trivial
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨z₁, s₁⟩, ⟨-, s₂⟩⟩, hz⟩ := hu
    have v₁ : eValid σ₁ = true := by simpa [eval, z₁] using hz
    have v₂ : eValid σ₂ = true := by
      rw [← v₁]; simp only [eValid, (hpub _ _ p₁ p₂ hp).2]
    exact ⟨⟨hpre _ _ s₁ p₁, (eValid_same s₁).trans v₁⟩, ⟨hpre _ _ s₂ p₂, (eValid_same s₂).trans v₂⟩,
      hpubS _ _ _ _ s₁ s₂ hp⟩

end VG.Proof.Rsa.X86_64

end

end

/-!
# `vg_rsa_public_checked` and `vg_rsa_public_precomputed_checked` on x86-64

Each is `vg_rsa_public`'s or `vg_rsa_public_precomputed`'s code guarded by
the check of `e` (`guarded`), against the contracts on the registers of
those functions with the checked postcondition (`pubChkContract`,
`pdChkContract`): `vg_rsa_public_checked`'s correctness and constant time
(`publicChecked_correct`, `publicChecked_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## The contracts on the registers -/

/-- `pubContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pubChkContract : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post s s' := Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- `pdContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pdChkContract : Contract isa where
  pre := pdContract.pre
  pub := pdContract.pub
  post s s' := ∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))

/-! ## What the contracts read of a state -/

theorem stackArg_same {s t : State} (h : Same s t) (i : Nat) : stackArg t i = stackArg s i := by
  simp only [stackArg, stackArgAddr, h.rsp, h.mem]

theorem pubPre_same {s t : State} (h : Same s t) : pubContract.pre t = pubContract.pre s := by
  simp only [pubContract, stackArg_same h, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    h.rd, h.wr]

theorem pdPre_same {s t : State} (h : Same s t) : pdContract.pre t = pdContract.pre s := by
  simp only [pdContract, stackArg_same h, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    h.rd, h.wr]

theorem pubPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : Same s₁ t₁) (h₂ : Same s₂ t₂) (h : pubContract.pub s₁ s₂) :
    pubContract.pub t₁ t₂ := by
  simp only [pubContract, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    stackArg_same h₁, stackArg_same h₂, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₁.mem,
    h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₂.mem] at h ⊢
  exact h

theorem pdPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : Same s₁ t₁) (h₂ : Same s₂ t₂) (h : pdContract.pub s₁ s₂) :
    pdContract.pub t₁ t₂ := by
  simp only [pdContract, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    stackArg_same h₁, stackArg_same h₂, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₁.mem,
    h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₂.mem] at h ⊢
  exact h

theorem pub_rsi {s : State} (h : pubContract.pre s) : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat := by
  simp only [pubContract] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hol, -⟩ := h
  exact hol

theorem pubGeom {s : State} (h : pubContract.pre s) : Geom s := by
  have c := codeCtx_of h
  have hsi := pub_rsi h
  have hk2 := c.hk2
  have hL2 := c.hL2
  refine ⟨by have := c.hk1; omega_using [hsi, this], by omega_using [hsi, hk2], fun j hj => c.hout j (by omega_using [hsi, hj]),
    fun b hb j hj => (c.hret b hb).2 j (by omega_using [hsi, hj]), c.hL1, by omega_using [hk2, hL2], fun i hi => c.heb.rd i (by
      rw [bytesAt_length]; exact hi)⟩

theorem pdGeom {s : State} (h : pdContract.pre s) : Geom s := by
  have c := pdCtx_of h
  have hk2 := c.hk2
  have hL2 := c.hL2
  exact ⟨by have := c.hk1; omega_using [this], by omega_using [hk2], c.hout, fun b hb j hj => (c.hret b hb).2 j hj, c.hL1, by omega_using [hk2, hL2],
    fun i hi => c.heb.rd i (by rw [bytesAt_length]; exact hi)⟩

/-! ## `vg_rsa_public_checked` -/

theorem publicChecked_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa publicChecked s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s' := by
  refine guarded_correct (fun s h _ => code_correct s h) (fun _ h => pubGeom h) (fun s t hs h => (pubPre_same hs).symm ▸ h) ?_ ?_ s h
  · intro s t s' _ hs hv hp
    simp only [pubContract, stackArg_same hs, hs.rdi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [pubChkContract, Spec.Rsa.publicOpChecked]
    simp only [eValid, eBytes] at hv
    simp only [hv, ↓reduceIte]; exact hp
  · intro s s' h hv hb hax
    have hsi := pub_rsi h
    simp only [eValid, eBytes] at hv
    simp only [pubChkContract, Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, by rw [← hsi]; exact hb⟩

theorem publicChecked_constantTime : ConstantTime isa pubContract.pre pubContract.pub publicChecked :=
  guarded_ct (fun _ _ _ _ _ _ p₁ p₂ => code_constantTime _ _ _ _ _ _ p₁.1 p₂.1) (fun _ h => pubGeom h) (fun s t hs h => (pubPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pubPub_same h₁ h₂ hp

/-! ## `vg_rsa_public_precomputed_checked` -/

end VG.Proof.Rsa.X86_64
