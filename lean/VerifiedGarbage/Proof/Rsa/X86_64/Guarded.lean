import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSA on x86-64: a function guarded by the check of its public exponent

`guarded c` runs `expCheck`, then `failOut` if `e` is not within
BoringSSL's limits and `c` if it is. `expCheck` changes only `rax`, `r10`,
`r11` and the flags, so `c` runs from a state that agrees with the entry
state on its arguments, memory and permissions (`Same`): for a contract `k`
of `c` that depends only on those, `guarded c` is correct
(`guarded_correct`) and constant time (`guarded_ct`) whenever `c` is.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

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

/-- `expCheck`, from the entry state. -/
theorem expCheck_entry {s : State} (g : Geom s) :
    WP isa expCheck s fun t => t.zf = some (eValid s) ∧ Same s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide +kernel) (expCheck_ok rfl (ofNat_toNat _).symm g.L1 g.L2 g.e rfl)
    fun t ⟨hz, hm, k⟩ hmx => ⟨hz, Same.of_keep k hm, fun r hr => k.gpr (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hmx⟩

/-- `guarded c` is correct if `c` is, from states agreeing with the entry
state (`hpre`): with `c`'s postcondition if `e` is valid (`hok`), with zeros
and 0 if not (`hfail`). -/
theorem guarded_correct {c : Prog isa} {k : Contract isa} {post : State → State → Prop}
    (hc : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
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
    obtain ⟨tr, s', he, habi, hp⟩ := hc t (hpre s t hs h)
    refine ⟨tr, s', he, ⟨fun r hr => (habi.1 r hr).trans (hcs r hr), ?_, ?_⟩, hok s t s' h hs hv hp⟩
    · rw [← hs.rsp, ← hs.mem]; exact habi.2.1
    · rw [habi.2.2, hmx]

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
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, s₁⟩, ⟨-, s₂⟩⟩, -⟩ := hu
    exact ⟨hpre _ _ s₁ p₁, hpre _ _ s₂ p₂, hpubS _ _ _ _ s₁ s₂ hp⟩

end VG.Proof.Rsa.X86_64
