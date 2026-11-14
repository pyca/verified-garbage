module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Scrubbing a registration that states what it writes (x86-64)

`Scrub.withScrubAll` scrubs a registration that states nothing of how much
of its arrays it writes (`Registration.written`); `withScrubAllW` scrubs one
that does, and keeps what it states: the clearing (`scrubTail`) writes only
the stack below the stack pointer, which no buffer of a contract that
`Sig.contract` derives overlaps (`bufs_stack`), so the scrubbed code changes
no byte of an array that the code did not (`writtenWithin_scrub`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

-- separate module: kept out of `Scrub.lean`, which many modules import, as `ScrubUp.lean` is

/-- An array of the parameters is one of their buffers. -/
theorem arrays_bufs : ∀ {ps : List (String × Param)} {vs : List (BitVec 64)} {n : String} {r : Region},
    (n, r) ∈ Sig.arrays ps vs → ∃ w, (r, w) ∈ Sig.bufs ps vs
  | [], _, _, _, h => by simp [Sig.arrays] at h
  | (_, .int ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .int ..) :: _, _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs] at h ⊢; exact arrays_bufs h
  | (_, .array ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .array m _ _) :: _, _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨-, rfl⟩ | h
    · exact ⟨m, .inl ⟨rfl, rfl⟩⟩
    · obtain ⟨w, hw⟩ := arrays_bufs h; exact ⟨w, .inr hw⟩
  | (_, .slice ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .slice ..) :: _, [_], _, _, h => by simp [Sig.arrays] at h
  | (_, .slice ..) :: _, _ :: _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs, List.mem_cons] at h ⊢
    obtain ⟨w, hw⟩ := arrays_bufs h; exact ⟨w, .inr hw⟩
  | (_, .slices ..) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .slices ..) :: _, [_], _, _, h => by simp [Sig.arrays] at h
  | (_, .slices ..) :: _, _ :: _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs] at h ⊢; exact arrays_bufs h
  | (_, .table _) :: _, [], _, _, h => by simp [Sig.arrays] at h
  | (_, .table _) :: _, _ :: _, _, _, h => by
    simp only [Sig.arrays, Sig.bufs] at h ⊢; exact arrays_bufs h

/-- The buffers of a contract that `Sig.contract` derives are apart from the
`stack` bytes below the stack pointer. -/
theorem bufs_stack {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) {vals : State → List (BitVec 64)}
    (hv : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals) (hst : stack ≠ 0) :
    ∀ b ∈ Sig.bufs sig.params (vals s),
      (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint b.1 := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals' hv'
  rw [hA.args, hA.ptrBits] at hv'
  obtain rfl := Option.some.inj (hv'.symm.trans hv)
  obtain ⟨-, -, -, -, hres, -⟩ := h
  intro b hb
  rw [hA.reserved] at hres
  refine hres _ ?_ b (List.mem_append_left _ (List.mem_append_left _ hb))
  cases stack with
  | zero => exact absurd rfl hst
  | succ n => simp [abi, stackBelow]

/-- `scrub` of code that changes no byte of its arrays past the bounds `W`
changes none either: its clearing writes only the stack below the stack
pointer, apart from every buffer. -/
theorem writtenWithin_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {c : Prog isa} {v f : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    {W : List (String × Nat)}
    (h : Verified target c (sig.contract A pre post wa stack leak)) (hcs : cs.sum = stack)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (ht : TailOk rb xs ps gs ks)
    (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (hW : ∀ s t s', (sig.contract A pre post wa stack leak).pre s → Exec isa c s t s' →
      Sig.writtenWithin abi sig W s s') :
    ∀ s t s', (sig.contract A pre post wa stack leak).pre s →
      Exec isa (scrub v rb xs ps gs ks cs c f) s t s' → Sig.writtenWithin abi sig W s s' := by
  intro s t s' hs he
  cases he with
  | seq a b =>
  rename_i u _ _
  obtain ⟨_, u', he', ha, -⟩ := h.1 s hs
  obtain ⟨-, rfl⟩ := Exec.det a he'
  have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
  have hl : cs.sum ≤ (u.gpr .rsp).toNat := by
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  obtain ⟨m', e, -, hu⟩ := tail_run v rb cs ht u hv hl (hev _ hl)
  obtain ⟨-, rfl⟩ := Exec.det b e
  have hw := hW s _ u hs a
  cases W with
  | nil => exact True.intro
  | cons w W =>
  simp only [Sig.writtenWithin] at hw ⊢
  revert hw
  cases hargs : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => exact fun _ => True.intro
  | some vals =>
  intro hw w' hw' b hb hn i hi hlt
  rw [← hw w' hw' b hb hn i hi hlt]
  show (finState v rb xs ps gs m' u f).mem _ = u.mem _
  rw [finState_other.1]
  refine hu _ fun hc => ?_
  have hc1 := hc.1
  rw [hr, hcs] at hc1
  have hst : stack ≠ 0 := by
    rintro rfl; simp [Region.Contains] at hc1
  obtain ⟨m, hm⟩ := arrays_bufs hb
  refine bufs_stack hA hs hargs hst _ hm _ hc1 ?_
  simp only [Region.Contains]
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega

/-- `scrubRegAll`, for a registration that may state how much of its arrays
it writes (`Registration.written`), which the scrubbed registration states
too. -/
def scrubRegAllW {api : Api} (r : Registration api target) (v : VecLevel)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hev : v = .evex → 16 ≤ r.stack ∧ r.code.all (fun i => !writesVec i) = false) : Registration api target :=
  let r₀ : Registration api target := { r with written := [], writtenOk := fun _ _ _ _ _ => True.intro }
  { scrubRegAll r₀ v hd hst h8 hlv hrb hpost hev rfl with
    written := r.written
    writtenOk := by
      obtain ⟨pre, post, leak, e⟩ := r.ofSig
      have hv := r.verified
      have hW := r.writtenOk
      have hE := (evexReg_all (c := r.code) h8 hst hev).2
      intro s t s' hs he
      have hs : r.contract.pre s := hs
      rw [e] at hv hW hs
      exact writtenWithin_scrub (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (chunks_sum r.stack)
        (chunks_valid h8) (tailOk_of _ _ _) hE hW s t s' hs he }

/-- `withScrubAll`, for a registration that may state how much of its
arrays it writes (`scrubRegAllW`). -/
def withScrubAllW {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let v := levelAll r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hev : v = .evex → 16 ≤ r.stack ∧ r.code.all (fun i => !writesVec i) = false then
    let r' := scrubRegAllW r v hd hst h8 hlv hrb hpost hev
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r

end VG.X86_64.Scrub
