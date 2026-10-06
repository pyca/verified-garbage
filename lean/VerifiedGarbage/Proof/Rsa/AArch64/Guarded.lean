import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck

/-!
# RSA on AArch64: a function guarded by the check of its public exponent

`guarded c` runs `expCheck`, then `failOut` if `e` is not within
BoringSSL's limits and `c` if it is. `expCheck` changes only `x9`–`x17` and
the flags, so `c` runs from a state that agrees with the entry state on its
arguments, memory and permissions (`Same`): for a contract `k` of `c` that
depends only on those, `guarded c` is correct (`guarded_correct`) and
constant time (`guarded_ct`) whenever `c` is.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `t` agrees with `s` on the argument registers, `sp`, memory and
permissions. -/
structure Same (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x0
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  x5 : t.gpr .x5 = s.gpr .x5
  x6 : t.gpr .x6 = s.gpr .x6
  x7 : t.gpr .x7 = s.gpr .x7
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The registers `expCheck` may change. -/
abbrev ecRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem Same.of_keep {s t : State} (k : Keep ecRegs s t) (hm : t.mem = s.mem) : Same s t :=
  ⟨k.gpr .x0 (by decide), k.gpr .x1 (by decide), k.gpr .x2 (by decide), k.gpr .x3 (by decide),
    k.gpr .x4 (by decide), k.gpr .x5 (by decide), k.gpr .x6 (by decide), k.gpr .x7 (by decide), k.sp, hm,
    k.rd, k.wr⟩

/-- The public exponent: the `x5` bytes at `x4`. -/
def eBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat

/-- Whether the public exponent is within BoringSSL's limits. -/
def eValid (s : State) : Bool := Spec.Rsa.exponentValid (Spec.Rsa.os2ip (eBytes s))

/-- What `guarded` needs of a state its contract allows: `out` (`x0`) of
`out_len` (`x1`) bytes, writable; `e` (`x4`) of `e_len` (`x5`) bytes,
readable. -/
structure Geom (s : State) : Prop where
  k1 : 1 ≤ (s.gpr .x1).toNat
  k2 : (s.gpr .x1).toNat < 2 ^ 63
  out : ∀ j < (s.gpr .x1).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  L1 : 1 ≤ (s.gpr .x5).toNat
  L2 : (s.gpr .x5).toNat < 2 ^ 63
  e : ∀ i < (s.gpr .x5).toNat, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 i) 1

/-- `expCheck`, from the entry state. -/
theorem expCheck_entry {s : State} (g : Geom s) :
    WP isa expCheck s fun t => t.gpr .x9 = BitVec.ofNat 64 (eValid s).toNat ∧ Same s t ∧ Keep ecRegs s t :=
  WP.mono (expCheck_ok rfl (ofNat_toNat64 _).symm g.L1 g.L2 g.e rfl)
    fun _ ⟨hz, hm, k⟩ => ⟨hz, Same.of_keep k hm, k⟩

/-- `abiPreserved` across `expCheck`, then code that preserves it. -/
theorem abi_of_keep {s t u : State} (k : Keep ecRegs s t) (h : abiPreserved t u) : abiPreserved s u :=
  ⟨fun r hr => (h.1 r hr).trans (k.gpr r (by revert r; decide)), h.2.1.trans k.sp,
    fun r hr => (h.2.2 r hr).trans (k.vcs r hr)⟩

/-- `guarded c` is correct if `c` is, from states agreeing with the entry
state (`hpre`): with `c`'s postcondition if `e` is valid (`hok`), with zeros
and 0 if not (`hfail`). -/
theorem guarded_correct {c : Prog isa} {k : Contract isa} {post : State → State → Prop}
    (hc : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hgeom : ∀ s, k.pre s → Geom s) (hpre : ∀ s t, Same s t → k.pre s → k.pre t)
    (hok : ∀ s t s', k.pre s → Same s t → eValid s = true → k.post t s' → post s s')
    (hfail : ∀ s s', k.pre s → eValid s = false →
      Spec.Rsa.bytesAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = List.replicate (s.gpr .x1).toNat 0 →
      s'.gpr .x0 = 0 → post s s')
    (s : State) (h : k.pre s) : ∃ t s', Exec isa (guarded c) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  have g := hgeom s h
  refine WP.seq (WP.mono (expCheck_entry g) fun t ⟨hz, hs, kt⟩ => ?_)
  refine WP.ite (!eValid s) (by rw [eval_zero, hz]; cases eValid s <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : eValid s = false := by simpa using hb
    refine WP.mono (failOut_ok (s := t) (op := s.gpr .x0) (k := (s.gpr .x1).toNat)
      hs.x0 (by rw [hs.x1, ofNat_toNat64]) g.k1 g.k2 (fun j hj => by rw [hs.wr]; exact g.out j hj))
      fun s' ⟨hb', hx0, _, k'⟩ => ⟨abi_of_keep kt ⟨fun r hr => k'.gpr r (by revert r; decide), k'.sp, k'.vcs⟩,
        hfail s s' h hv hb' hx0⟩
  · have hv : eValid s = true := by simpa using hb
    obtain ⟨tr, s', he, habi, hp⟩ := hc t (hpre s t hs h)
    exact ⟨tr, s', he, abi_of_keep kt habi, hok s t s' h hs hv hp⟩

/-- Two runs of `c` from states its contract allows and agreeing on its
public data leak the same. -/
theorem relCT_of_ct {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (h : ConstantTime isa pre pub c) :
    RelCT isa (fun s₁ s₂ => pre s₁ ∧ pre s₂ ∧ pub s₁ s₂) c fun _ _ => True :=
  fun _ _ _ _ _ _ ⟨p₁, p₂, hp⟩ e₁ e₂ => ⟨h _ _ _ _ _ _ p₁ p₂ hp e₁ e₂, trivial⟩

/-- `guarded c` is constant time if `c` is: `expCheck` and `failOut` by the
taint analysis, from the pointers and lengths, and the branch on public
data. -/
theorem guarded_ct {c : Prog isa} {k : Contract isa} (hct : ConstantTime isa k.pre k.pub c)
    (hgeom : ∀ s, k.pre s → Geom s) (hpre : ∀ s t, Same s t → k.pre s → k.pre t)
    (hpub : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.x0, .x1, .x4, .x5], s₁.gpr r = s₂.gpr r) ∧ eBytes s₁ = eBytes s₂)
    (hpubS : ∀ s₁ s₂ t₁ t₂, Same s₁ t₁ → Same s₂ t₂ → k.pub s₁ s₂ → k.pub t₁ t₂) :
    ConstantTime isa k.pre k.pub (guarded c) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hexp := (RelCT.taint (A := taint) (Taint.ofRegs [.x4, .x5])
    (P := fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂)
    (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨(hpub _ _ p₁ p₂ hp).1, fun r hr => (hpub _ _ p₁ p₂ hp).2.1 r (by
      have := RegSet.mem_ofList.mp hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      rcases this with rfl | rfl <;> simp)⟩) (by taint_decide)).wpDep
    (F := fun (s t : State) => t.gpr .x9 = BitVec.ofNat 64 (eValid s).toNat ∧ Same s t)
    fun s₁ s₂ ⟨p₁, p₂, _⟩ => ⟨WP.mono (expCheck_entry (hgeom _ p₁)) fun _ h => ⟨h.1, h.2.1⟩,
      WP.mono (expCheck_entry (hgeom _ p₂)) fun _ h => ⟨h.1, h.2.1⟩⟩
  refine RelCT.seq hexp (RelCT.ite ?_ ?_ ?_)
  · rintro u₁ u₂ ⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨z₁, -⟩, ⟨z₂, -⟩⟩
    show isa.eval _ u₁ = isa.eval _ u₂
    rw [eval_zero, eval_zero, z₁, z₂, eValid, eValid, (hpub _ _ p₁ p₂ hp).2.2]
  · refine (RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1]) (fun u₁ u₂ hu => ?_) (by taint_decide)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, s₁⟩, ⟨-, s₂⟩⟩, -⟩ := hu
    have hr := (hpub _ _ p₁ p₂ hp).2.1
    refine ⟨by rw [s₁.sp, s₂.sp]; exact (hpub _ _ p₁ p₂ hp).1, fun r hr' => ?_⟩
    have := RegSet.mem_ofList.mp hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · rw [s₁.x0, s₂.x0]; exact hr _ (by simp)
    · rw [s₁.x1, s₂.x1]; exact hr _ (by simp)
  · refine (relCT_of_ct hct).mono (fun u₁ u₂ hu => ?_) fun _ _ _ => trivial
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, s₁⟩, ⟨-, s₂⟩⟩, -⟩ := hu
    exact ⟨hpre _ _ s₁ p₁, hpre _ _ s₂ p₂, hpubS _ _ _ _ s₁ s₂ hp⟩

end VG.Proof.Rsa.AArch64
