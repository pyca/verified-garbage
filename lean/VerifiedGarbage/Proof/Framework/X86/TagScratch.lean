import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.TagScratch

/-!
# A tag passed through a buffer on the stack (x86)

`Verified.tagScratch`: code verified for a function one of whose parameters,
number `q`, is a buffer of working space whose first 16 bytes also carry a
tag in or out (its contract on `sig.tagWork q …`), runs as a function whose
parameter there is a pointer to the 16-byte tag alone, when `withTagScratch`
allocates the buffer in a frame on the stack, with `bytes` more bytes of
stack. Every argument is on the stack, so the frame holds what the code
expects at and above `esp` on entry, as `withStackScratch`'s does (a word for
its return address and a copy of the argument slots), then the tag pointer
and the buffer. Before the code, the frame copies the tag into the buffer and
passes the buffer in the tag pointer's slot of the copy (`tagSetup`); after
it, it copies the buffer's first 16 bytes back to the tag (`tagOut`). The
code runs from the state after `tagSetup`, with the permissions of its
contract (`narrowT`), and its run there is its run from that state
(`Exec.widen`).

The frame, of `bytes` bytes from `esp` after its push: a word standing for
the code's return address; the copy of the `slots sig` argument slots (from
`esp + 4`), with the buffer's address in the tag pointer's slot
(`tagSlot sig q`, after the slots of the arguments before it: a 64-bit
integer takes two); the tag pointer (at `esp + 4 + 4 * slots sig`); and the
buffer (from `esp + 8 + 4 * slots sig`), the rest of the frame. The copies
go through `eax`, the tag through `ecx` and `xmm0`; `tagOut` changes only
`ecx` and `xmm0`, so the code's result (`edx:eax`) is the function's.

The two contracts are related by `Sig.TagFrame` (`Proof/Framework/TagScratch.lean`),
on the arguments before the tag (`vals s (preWidths sig q) 0`) and after it
(`vals s (postWidths sig q) (tagSlot sig q + 1)`).
-/

namespace VG.X86

open VG.Impl.StackScratch.X86

/-! ## The blocks -/

/-- Byte `i` of a copied 16 bytes. -/
theorem Mem.writeW_readW128_apply (m₀ m : Mem) (w t : Addr) {i : Nat} (hi : i < 16) :
    (m.writeW w (m₀.readW t 128)) (w + BitVec.ofNat 64 i) = m₀ (t + BitVec.ofNat 64 i) := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat w (show i < 2 ^ 64 by omega),
    show i < 128 / 8 by omega, ite_true, Mem.readW, show 128 / 8 = 16 from rfl]
  rw [show (BitVec.setWidth (8 * 16) (BitVec.setWidth 128 (Mem.read m₀ t 16))) = Mem.read m₀ t 16 by
    simp]
  exact Mem.extractLsb'_read m₀ t hi

/-- A 16-byte write leaves the other bytes. -/
theorem Mem.writeW128_apply_of_not {m : Mem} {w x : Addr} {v : BitVec 128}
    (h : ¬ (x - w).toNat < 16) : (m.writeW w v) x = m x := by
  simp only [Mem.writeW, Mem.write, show 128 / 8 = 16 from rfl, h, ite_false]

theorem addr_zero (x : BitVec 32) : addr x 0 = x.setWidth 64 := by
  simp [addr]

/-- The memory after `loadTag`, `tagIn` and `pointTag`, from memory `M` with
`esp = sp`, for the tag pointer `t`. -/
def tailMem (n j : Nat) (M : Mem) (sp t : BitVec 32) : Mem :=
  let M₁ := M.writeW (addr sp (4 + 4 * n)) t
  let M₂ := M₁.writeW (addr sp (8 + 4 * n)) (M₁.readW (t.setWidth 64) 128)
  M₂.writeW (addr sp (4 + 4 * j)) (sp + BitVec.ofNat 32 (8 + 4 * n))

/-- `loadTag`, `tagIn` and `pointTag`, from `u` (after the copies): only
`eax`, `ecx`, `xmm0` and the flags changed, and memory `tailMem`. -/
theorem tagTail_run {bytes n j : Nat} {u : State}
    (h₁ : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 4)
    (h₂ : InRegions u.wr (addr (u.gpr .esp) (4 + 4 * n)) 4)
    (h₃ : InRegions (u.rd ++ u.wr)
      ((u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32).setWidth 64) 16)
    (h₄ : InRegions u.wr (addr (u.gpr .esp) (8 + 4 * n)) 16)
    (h₅ : InRegions u.wr (addr (u.gpr .esp) (4 + 4 * j)) 4) :
    ∃ w', execBlock isa (loadTag bytes j ++ tagIn n ++ pointTag n j) u =
        some (w', [.addr (addr (u.gpr .esp) (bytes + 4 + 4 * j)), .addr (addr (u.gpr .esp) (4 + 4 * n)),
          .addr ((u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32).setWidth 64),
          .addr (addr (u.gpr .esp) (8 + 4 * n)), .addr (addr (u.gpr .esp) (4 + 4 * j))]) ∧
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ (∀ q, q ≠ .eax → q ≠ .ecx → w'.gpr q = u.gpr q) ∧
      w'.mem = tailMem n j u.mem (u.gpr .esp) (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32) := by
  simp only [loadTag, tagIn, pointTag, List.cons_append, List.nil_append,
    execBlock, isa, exec, readSrc, State.load32, State.store32, State.load128, State.store128, ea_mk,
    Option.map_some, execAlu, Option.bind_some, addrs, srcAddrs]
  simp [h₁, h₂, h₃, h₄, h₅, State.setReg, State.setXmm, arithFlags, State.setFlags, addr_zero,
    tailMem]
  intro q h₁ h₂; simp [h₁, h₂]

/-- The memory after `tagOut n`, from memory `M` with `esp = sp`: the 16
bytes at `sp + 8 + 4n` copied to the tag whose pointer is at `sp + 4 + 4n`. -/
def tagOutMem (n : Nat) (M : Mem) (sp : BitVec 32) : Mem :=
  M.writeW ((M.readW (addr sp (4 + 4 * n)) 32).setWidth 64) (M.readW (addr sp (8 + 4 * n)) 128)

theorem tagOut_run {n : Nat} {u : State}
    (h₁ : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (4 + 4 * n)) 4)
    (h₂ : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (8 + 4 * n)) 16)
    (h₃ : InRegions u.wr ((u.mem.readW (addr (u.gpr .esp) (4 + 4 * n)) 32).setWidth 64) 16) :
    ∃ u', execBlock isa (tagOut n) u = some (u',
        [.addr (addr (u.gpr .esp) (4 + 4 * n)), .addr (addr (u.gpr .esp) (8 + 4 * n)),
          .addr ((u.mem.readW (addr (u.gpr .esp) (4 + 4 * n)) 32).setWidth 64)]) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mem = tagOutMem n u.mem (u.gpr .esp) ∧
      (∀ q, q ≠ .ecx → u'.gpr q = u.gpr q) := by
  simp only [tagOut, execBlock, isa, exec, readSrc, State.load32, State.load128, State.store128,
    ea_mk, Option.map_some, addrs, srcAddrs]
  simp [h₁, h₂, h₃, State.setReg, State.setXmm, addr_zero, tagOutMem]
  intro q h; simp [h]

/-- What `loadTag`, `tagIn` and `pointTag` leave in memory, if the tag lies
outside the 20 bytes from `esp + 4 + 4n` (the saved pointer and the buffer's
first 16 bytes): written only within the copies and those 20 bytes, the
buffer's address in slot `j`, the pointer saved, and the tag's bytes in the
buffer. -/
theorem tailMem_facts {n j : Nat} {M : Mem} {sp t : BitVec 32} (hfit : sp.toNat + 24 + 4 * n < 2 ^ 32)
    (hj : j < n)
    (hd : (⟨t.setWidth 64, 16⟩ : Region).Disjoint ⟨sp.setWidth 64 + BitVec.ofNat 64 (4 + 4 * n), 20⟩) :
    Frame [⟨sp.setWidth 64 + 4, 4 * n + 20⟩] M (tailMem n j M sp t) ∧
      (tailMem n j M sp t).readW (addr sp (4 + 4 * n)) 32 = t ∧
      (∀ i < n, (tailMem n j M sp t).readW (addr sp (4 + 4 * i)) 32 =
        if i = j then sp + BitVec.ofNat 32 (8 + 4 * n) else M.readW (addr sp (4 + 4 * i)) 32) ∧
      ∀ i < 16, tailMem n j M sp t (sp.setWidth 64 + BitVec.ofNat 64 (8 + 4 * n) + BitVec.ofNat 64 i) =
        M (t.setWidth 64 + BitVec.ofNat 64 i) := by
  have hA : ∀ {d : Nat}, d ≤ 24 + 4 * n → addr sp d = sp.setWidth 64 + BitVec.ofNat 64 d :=
    fun h => addr_eq (by omega)
  generalize sp.setWidth 64 = P at hd ⊢ hA
  have h4 : P + 4 = P + BitVec.ofNat 64 4 := rfl
  have hsub : ∀ {d k : Nat}, 4 ≤ d → d + k ≤ 4 * n + 24 →
      ∀ r ∈ ([⟨P + BitVec.ofNat 64 d, k⟩] : List Region),
        ∃ r' ∈ ([⟨P + 4, 4 * n + 20⟩] : List Region), Region.Sub r r' := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [h4]; exact Offset.sub _ h₁ (by omega)⟩
  have hmem : tailMem n j M sp t =
      ((M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t).writeW (P + BitVec.ofNat 64 (8 + 4 * n))
        ((M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t).readW (t.setWidth 64) 128)).writeW
          (P + BitVec.ofNat 64 (4 + 4 * j)) (sp + BitVec.ofNat 32 (8 + 4 * n)) := by
    simp only [tailMem, hA (show 4 + 4 * n ≤ 24 + 4 * n by omega),
      hA (show 8 + 4 * n ≤ 24 + 4 * n by omega), hA (show 4 + 4 * j ≤ 24 + 4 * n by omega)]
  have hA' : ∀ i < n, addr sp (4 + 4 * i) = P + BitVec.ofNat 64 (4 + 4 * i) := fun i hi => hA (by omega)
  rw [hmem, hA (by omega)]
  have f₁ : Frame [⟨P + BitVec.ofNat 64 (4 + 4 * n), 4⟩] M (M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hr₁ : (M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t).readW (P + BitVec.ofNat 64 (4 + 4 * n)) 32 = t :=
    Mem.readW_writeW_self32 _ _ _
  have ht₁ : ∀ i < 16, (M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t) (t.setWidth 64 + BitVec.ofNat 64 i) =
      M (t.setWidth 64 + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨t.setWidth 64, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd.sub_right (Offset.sub _ (Nat.le_refl _) (by omega))) (show 16 ≤ 2 ^ 64 by decide) hi
  have hv₁ : ∀ i < n, (M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t).readW (P + BitVec.ofNat 64 (4 + 4 * i)) 32 =
      M.readW (P + BitVec.ofNat 64 (4 + 4 * i)) 32 := fun i hi =>
    Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)
  generalize M.writeW (P + BitVec.ofNat 64 (4 + 4 * n)) t = M₁ at f₁ hr₁ ht₁ hv₁
  have f₂ : Frame [⟨P + BitVec.ofNat 64 (8 + 4 * n), 16⟩] M₁
      (M₁.writeW (P + BitVec.ofNat 64 (8 + 4 * n)) (M₁.readW (t.setWidth 64) 128)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hw₂ := fun i (hi : i < 16) =>
    Mem.writeW_readW128_apply M₁ M₁ (P + BitVec.ofNat 64 (8 + 4 * n)) (t.setWidth 64) hi
  have hr₂ : (M₁.writeW (P + BitVec.ofNat 64 (8 + 4 * n)) (M₁.readW (t.setWidth 64) 128)).readW
      (P + BitVec.ofNat 64 (4 + 4 * n)) 32 = t := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), hr₁]
  have hv₂ : ∀ i < n, (M₁.writeW (P + BitVec.ofNat 64 (8 + 4 * n)) (M₁.readW (t.setWidth 64) 128)).readW
      (P + BitVec.ofNat 64 (4 + 4 * i)) 32 = M.readW (P + BitVec.ofNat 64 (4 + 4 * i)) 32 := fun i hi => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), hv₁ i hi]
  generalize M₁.writeW (P + BitVec.ofNat 64 (8 + 4 * n)) (M₁.readW (t.setWidth 64) 128) = M₂ at f₂ hw₂ hr₂ hv₂
  have f₃ : Frame [⟨P + BitVec.ofNat 64 (4 + 4 * j), 4⟩] M₂
      (M₂.writeW (P + BitVec.ofNat 64 (4 + 4 * j)) (sp + BitVec.ofNat 32 (8 + 4 * n))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨((f₁.sub (hsub (by omega) (by omega))).trans (f₂.sub (hsub (by omega) (by omega)))).trans
      (f₃.sub (hsub (by omega) (by omega))), ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by omega)) (by omega) (by omega)) (by decide), hr₂]
  · rw [hA' i hi]
    split
    · next h => subst h; exact Mem.readW_writeW_self32 _ _ _
    · next h =>
      rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hv₂ i hi]
  · rw [f₃.bytes (R := ⟨P + BitVec.ofNat 64 (8 + 4 * n), 16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (show 16 ≤ 2 ^ 64 by decide) hi,
      hw₂ i hi, ht₁ i hi]

/-- The addresses `tagSetup bytes n j` accesses, from `esp = sp`, for the tag
pointer `t`. -/
def tagSetupTrace (bytes n j : Nat) (sp t : BitVec 32) : List Leak :=
  copyTrace bytes sp n ++ [.addr (addr sp (bytes + 4 + 4 * j)), .addr (addr sp (4 + 4 * n)),
    .addr (t.setWidth 64), .addr (addr sp (8 + 4 * n)), .addr (addr sp (4 + 4 * j))]

/-- The state after `tagSetup bytes n j` from `u`, if it runs. -/
def tagSetupState (bytes n j : Nat) (u : State) : State :=
  ((execBlock isa (tagSetup bytes n j) u).map Prod.fst).getD u

/-- `tagSetup`, from the state after the frame's push (`u`, whose `esp` is
the frame's base): the argument slots copied into the frame, the buffer's
address in slot `j` of the copy, the tag pointer saved after them and the tag
copied to the buffer after that; nothing else written, and only `eax` and
`ecx` (of the general-purpose registers) changed. -/
theorem tagSetup_run {bytes n j : Nat} {u : State}
    (hfit : (u.gpr .esp).toNat + bytes + 4 + 4 * n ≤ 2 ^ 32) (hb : 24 + 4 * n ≤ bytes) (hj : j < n)
    (hF : (⟨(u.gpr .esp).setWidth 64, bytes⟩ : Region) ∈ u.wr)
    (hr : ∀ i < n, InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * i)) 4)
    (htw : (⟨(u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32).setWidth 64, 16⟩ : Region) ∈ u.wr)
    (htd : (⟨(u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32).setWidth 64, 16⟩ : Region).Disjoint
      ⟨(u.gpr .esp).setWidth 64, bytes⟩) :
    execBlock isa (tagSetup bytes n j) u = some (tagSetupState bytes n j u,
        tagSetupTrace bytes n j (u.gpr .esp) (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32)) ∧
      (tagSetupState bytes n j u).rd = u.rd ∧ (tagSetupState bytes n j u).wr = u.wr ∧
      (∀ q, q ≠ .eax → q ≠ .ecx → (tagSetupState bytes n j u).gpr q = u.gpr q) ∧
      Frame [⟨(u.gpr .esp).setWidth 64 + 4, 4 * n + 20⟩] u.mem (tagSetupState bytes n j u).mem ∧
      (∀ i < n, (tagSetupState bytes n j u).mem.readW (addr (u.gpr .esp) (4 + 4 * i)) 32 =
        if i = j then u.gpr .esp + BitVec.ofNat 32 (8 + 4 * n)
        else u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * i)) 32) ∧
      (tagSetupState bytes n j u).mem.readW (addr (u.gpr .esp) (4 + 4 * n)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32 ∧
      ∀ i < 16, (tagSetupState bytes n j u).mem
          ((u.gpr .esp).setWidth 64 + BitVec.ofNat 64 (8 + 4 * n) + BitVec.ofNat 64 i) =
        u.mem ((u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32).setWidth 64 + BitVec.ofNat 64 i) := by
  have hA : ∀ {d : Nat}, d < bytes + 4 + 4 * n → addr (u.gpr .esp) d =
      (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun h => addr_eq (by omega)
  have hc : ∀ {d k : Nat}, d + k ≤ bytes → InRegions u.wr (addr (u.gpr .esp) d) k :=
    fun h => ⟨_, hF, by rw [hA (by omega)]; exact Offset.contains_base _ h (by omega)⟩
  have h4 : (u.gpr .esp).setWidth 64 + 4 = (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := rfl
  -- The copies.
  have hcp := copies_run (bytes := bytes) (u := u) n hr (fun i hi => hc (by omega))
  obtain ⟨f₁, hv₁⟩ := copiedState_mem (bytes := bytes) (u := u) n (by omega) (by omega)
  have e₁ := copiedState_esp bytes u n
  have r₁ := copiedState_rd bytes u n
  have w₁ := copiedState_wr bytes u n
  have g₁ : ∀ q, q ≠ .eax → (copiedState bytes u n).gpr q = u.gpr q :=
    fun q h => copiedState_gpr bytes u h n
  generalize copiedState bytes u n = u₁ at hcp f₁ hv₁ e₁ r₁ w₁ g₁
  generalize ht : u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32 = t at htw htd ⊢
  have ht₁ : u₁.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32 = t := by
    rw [← ht, hA (by omega)]
    refine f₁.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [h4]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have htb : ∀ i < 16, u₁.mem (t.setWidth 64 + BitVec.ofNat 64 i) = u.mem (t.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₁.bytes (R := ⟨t.setWidth 64, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h4]; exact htd.sub_right (Offset.sub_base _ (by omega))) (show 16 ≤ 2 ^ 64 by decide) hi
  -- The tail.
  obtain ⟨u₂, hrun₂, r₂, w₂, g₂, m₂⟩ := tagTail_run (bytes := bytes) (n := n) (j := j) (u := u₁)
    (by rw [r₁, w₁, e₁]; exact hr j hj) (by rw [w₁, e₁]; exact hc (by omega))
    (by rw [e₁, ht₁]; exact ⟨_, List.mem_append_right _ (w₁ ▸ htw), Region.contains_self _ _⟩)
    (by rw [w₁, e₁]; exact hc (by omega)) (by rw [w₁, e₁]; exact hc (by omega))
  rw [e₁, ht₁] at hrun₂ m₂
  obtain ⟨f₂, hs₂, hv₂, hW₂⟩ := tailMem_facts (n := n) (j := j) (M := u₁.mem) (sp := u.gpr .esp) (t := t)
    (by omega) hj (htd.sub_right (Offset.sub_base _ (by omega)))
  rw [← m₂] at f₂ hs₂ hv₂ hW₂
  have hrun : execBlock isa (tagSetup bytes n j) u =
      some (u₂, tagSetupTrace bytes n j (u.gpr .esp) t) := by
    rw [tagSetup, List.append_assoc, List.append_assoc, execBlock_append, hcp]
    simp only [Option.bind_some, ← List.append_assoc, hrun₂, Option.map_some, tagSetupTrace]
  have hst : tagSetupState bytes n j u = u₂ := by simp [tagSetupState, hrun]
  rw [hst]
  refine ⟨hrun, r₂.trans r₁, w₂.trans w₁, fun q h₁ h₂ => by rw [g₂ q h₁ h₂, g₁ q h₁], ?_,
    fun i hi => ?_, hs₂, fun i hi => by rw [hW₂ i hi, htb i hi]⟩
  · refine (f₁.sub fun r hr => ?_).trans f₂
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  · rw [hv₂ i hi]
    split
    · rfl
    · exact hv₁ i hi

/-! ## The arguments around the tag -/

/-- The widths of the arguments before parameter `q`. -/
def preWidths (sig : Sig) (q : Nat) : List Nat :=
  (Sig.psWords (sig.params.take q) abi.ptrBits).map (·.bits abi.ptrBits)

/-- The widths of the arguments after parameter `q`. -/
def postWidths (sig : Sig) (q : Nat) : List Nat :=
  (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).map (·.bits abi.ptrBits)

/-- The argument slot of parameter `q`. -/
def tagSlot (sig : Sig) (q : Nat) : Nat := ((preWidths sig q).map (· / 32)).sum

/-- The values of arguments of widths `ws` from slot `i` on. -/
def vals (s : State) (ws : List Nat) (i : Nat) : List (BitVec 64) :=
  (ws.zip (argSlots ws i)).map fun (w, i) => argVal s w i

theorem argSlots_append' : ∀ (ws₁ ws₂ : List Nat) (i : Nat),
    argSlots (ws₁ ++ ws₂) i = argSlots ws₁ i ++ argSlots ws₂ (i + (ws₁.map (· / 32)).sum)
  | [], _, i => by simp [argSlots]
  | w :: ws, ws₂, i => by
    simp only [List.cons_append, argSlots, argSlots_append' ws ws₂, List.map_cons, List.sum_cons,
      Nat.add_assoc]

theorem vals_length (s : State) (ws : List Nat) (i : Nat) : (vals s ws i).length = ws.length := by
  simp [vals, argSlots_length]

/-- The values of arguments read from slots on which two states agree. -/
theorem vals_congr {s s' : State} (ws : List Nat) (i : Nat) (hw : ∀ w ∈ ws, w = 32 ∨ w = 64)
    (h : ∀ k, i ≤ k → k < i + (ws.map (· / 32)).sum → arg s k = arg s' k) :
    vals s ws i = vals s' ws i := by
  induction ws generalizing i with
  | nil => simp only [vals, argSlots, List.zip_nil_left, List.map_nil]
  | cons w ws ih =>
    have ih' := ih (i + w / 32) (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
      fun k h₁ h₂ => h k (by omega) (by simp only [List.map_cons, List.sum_cons]; omega)
    have h0 := h i (Nat.le_refl _) (by
      simp only [List.map_cons, List.sum_cons]; rcases hw w (List.mem_cons_self ..) with rfl | rfl <;> omega)
    have hd : argVal s w i = argVal s' w i := by
      rcases hw w (List.mem_cons_self ..) with rfl | rfl
      · simp only [argVal, show (32 : Nat) ≠ 64 by decide, ite_false, h0]
      · have h1 := h (i + 1) (by omega) (by simp only [List.map_cons, List.sum_cons]; omega)
        simp only [argVal, ite_true, h0, h1]
    simp only [vals, argSlots, List.zip_cons_cons, List.map_cons] at ih' ⊢
    rw [ih', hd]

section
variable {sig : Sig} {q : Nat} {nmT nm : String} {e : Elem} {n : Nat}

theorem widths_split (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    widths sig = preWidths sig q ++ 32 :: postWidths sig q := by
  rw [widths, Sig.words_split _ hq, List.map_append, List.map_cons]
  rfl

theorem widths_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    widths (sig.tagWork q nm e n) = widths sig := by
  rw [widths, widths, Sig.words_tagWork _ _ _ _ hq]

theorem slots_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    slots (sig.tagWork q nm e n) = slots sig := by
  rw [slots, slots, widths_tagWork hq]

theorem stackArgs_tagWork (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) :
    stackArgs (sig.tagWork q nm e n) s = stackArgs sig s := by
  rw [stackArgs, stackArgs, widths_tagWork hq]

theorem slots_split (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    slots sig = tagSlot sig q + 1 + ((postWidths sig q).map (· / 32)).sum := by
  rw [slots, widths_split hq, List.map_append, List.sum_append, List.map_cons, List.sum_cons, tagSlot]
  omega

theorem preWidths_mem (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    ∀ w ∈ preWidths sig q, w = 32 ∨ w = 64 := fun w hw =>
  widths_mem sig w (by rw [widths_split hq]; exact List.mem_append_left _ hw)

theorem postWidths_mem (hq : sig.params[q]? = some (nmT, .array true .u8 16)) :
    ∀ w ∈ postWidths sig q, w = 32 ∨ w = 64 := fun w hw =>
  widths_mem sig w (by rw [widths_split hq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hw))

/-- The arguments of `sig`: those before the tag, the tag pointer (in slot
`tagSlot sig q`) and those after it. -/
theorem stackArgs_split (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) :
    stackArgs sig s = vals s (preWidths sig q) 0 ++
      (arg s (tagSlot sig q)).setWidth 64 :: vals s (postWidths sig q) (tagSlot sig q + 1) := by
  unfold stackArgs
  rw [widths_split hq, argSlots_append', List.zip_append (by rw [argSlots_length]), List.map_append]
  simp only [Nat.zero_add, argSlots, List.zip_cons_cons, List.map_cons, vals, tagSlot, argVal,
    show (32 : Nat) ≠ 64 by decide, ite_false]

theorem vals_pre_length (s : State) :
    (vals s (preWidths sig q) 0).length = (Sig.psWords (sig.params.take q) abi.ptrBits).length := by
  rw [vals_length, preWidths, List.length_map]

theorem vals_post_length (s : State) (i : Nat) :
    (vals s (postWidths sig q) i).length = (Sig.psWords (sig.params.drop (q + 1)) abi.ptrBits).length := by
  rw [vals_length, postWidths, List.length_map]

/-- The arguments of two states that agree on every slot but the tag
pointer's, around it. -/
theorem stackArgs_congr (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s s' : State}
    (h : ∀ k < slots sig, k ≠ tagSlot sig q → arg s k = arg s' k) :
    stackArgs sig s = vals s' (preWidths sig q) 0 ++
      (arg s (tagSlot sig q)).setWidth 64 :: vals s' (postWidths sig q) (tagSlot sig q + 1) := by
  have hs := slots_split hq
  rw [stackArgs_split hq, vals_congr _ _ (preWidths_mem hq) fun k _ hk => h k (by
      rw [hs]; simp only [tagSlot]; omega) (by simp only [tagSlot]; omega),
    vals_congr _ _ (postWidths_mem hq) fun k hk₁ hk₂ => h k (by omega) (by omega)]

/-- The buffers of the function and of the code: those of the function
around the tag, and the code's with the buffer (at `W`) in its place. -/
theorem tag_bufs (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) (W : Addr) :
    Sig.bufs sig.params (stackArgs sig s) =
        Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++
          (⟨(arg s (tagSlot sig q)).setWidth 64, 16⟩, true) ::
            Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1)) ∧
      Sig.bufs (sig.tagWork q nm e n).params
          (vals s (preWidths sig q) 0 ++ W :: vals s (postWidths sig q) (tagSlot sig q + 1)) =
        Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++ (⟨W, n * e.size⟩, true) ::
          Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1)) :=
  ⟨by rw [stackArgs_split hq]; exact Sig.bufs_split abi.ptrBits hq _ _ _ (vals_pre_length s),
    Sig.bufs_tagWork nm e n abi.ptrBits hq _ _ _ (vals_pre_length s)⟩

end

/-! ## The state the code runs from -/

section
variable {sig : Sig} {q : Nat} {nmT nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {wa : Bool} {stack bytes : Nat}

/-- The buffer's address, from the state `s` on entry. -/
abbrev tagBuf (sig : Sig) (bytes : Nat) (s : State) : BitVec 32 :=
  s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)

/-- The code's arguments, from the state `s` on entry: the function's, with
the buffer in the tag pointer's place. -/
def innerArgs (sig : Sig) (q bytes : Nat) (s : State) : List (BitVec 64) :=
  vals s (preWidths sig q) 0 ++ (tagBuf sig bytes s).setWidth 64 ::
    vals s (postWidths sig q) (tagSlot sig q + 1)

/-- The regions of the code's contract, from the state `s` on entry: the
buffers, with the working space in the tag's place, and the copy of the
arguments. -/
def innerRegions (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (wa : Bool)
    (s : State) : List (Region × Bool) :=
  Sig.bufs (sig.tagWork q nm e n).params (innerArgs sig q bytes s) ++
    [(⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64, 4 * slots sig⟩, wa)]

/-- The state the code runs from, with the permissions of its contract: the
state after the frame's push and `tagSetup`. -/
def narrowT (sig : Sig) (q : Nat) (nm : String) (e : Elem) (n bytes : Nat) (wa : Bool) (s : State) :
    State :=
  (tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s)).withRegions
    (((innerRegions sig q nm e n bytes wa s).filter (!·.2)).map (·.1))
    (((innerRegions sig q nm e n bytes wa s).filter (·.2)).map (·.1))

theorem narrowT_gpr (s : State) : (narrowT sig q nm e n bytes wa s).gpr =
    (tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s)).gpr :=
  State.withRegions_gpr _ _ _
theorem narrowT_mem (s : State) : (narrowT sig q nm e n bytes wa s).mem =
    (tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s)).mem :=
  State.withRegions_mem _ _ _

theorem tagSlot_lt (hq : sig.params[q]? = some (nmT, .array true .u8 16)) : tagSlot sig q < slots sig := by
  rw [slots_split hq]; omega

/-- What `tagSetup` gives, from a state satisfying the function's
precondition: the run, from the frame's push; and the state the code runs
from, which keeps what the function must keep, passes the arguments with
the buffer in the tag pointer's place, and holds the tag pointer after the
copied arguments and the tag in the buffer, having written only there. -/
theorem narrowT_facts (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) (hl : Sig.noLists sig.params = true) :
    execBlock isa (tagSetup bytes (slots sig) (tagSlot sig q)) (allocState bytes s) =
        some (tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s),
          tagSetupTrace bytes (slots sig) (tagSlot sig q) (s.gpr .esp - BitVec.ofNat 32 bytes)
            (arg s (tagSlot sig q))) ∧
      (tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s)).rd = (allocState bytes s).rd ∧
      (tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s)).wr = (allocState bytes s).wr ∧
      (narrowT sig q nm e n bytes wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esp → (narrowT sig q nm e n bytes wa s).gpr r = s.gpr r) ∧
      stackArgs (sig.tagWork q nm e n) (narrowT sig q nm e n bytes wa s) = innerArgs sig q bytes s ∧
      Frame [⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 + 4, 4 * slots sig + 20⟩] s.mem
        (narrowT sig q nm e n bytes wa s).mem ∧
      (narrowT sig q nm e n bytes wa s).mem.readW
          (addr (s.gpr .esp - BitVec.ofNat 32 bytes) (4 + 4 * slots sig)) 32 = arg s (tagSlot sig q) ∧
      ∀ i < 16, (narrowT sig q nm e n bytes wa s).mem ((tagBuf sig bytes s).setWidth 64 + BitVec.ofNat 64 i) =
        s.mem ((arg s (tagSlot sig q)).setWidth 64 + BitVec.ofNat 64 i) := by
  have hj := tagSlot_lt hq
  obtain ⟨hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s 0
  rw [pre_stack hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hE : (s.gpr .esp - BitVec.ofNat 32 bytes).toNat = (s.gpr .esp).toNat - bytes := sub_toNat (by omega)
  have hesp : (allocState bytes s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes := allocState_esp _ _
  have hsrc : ∀ i, addr (s.gpr .esp - BitVec.ofNat 32 bytes) (bytes + 4 + 4 * i) = argAddr s i := fun i => by
    simp only [addr, argAddr]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [show bytes + 4 + 4 * i = bytes + (4 + 4 * i) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  have hsp : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes := Taint.sub_setWidth (by omega)
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
        List Region) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  -- The caller's argument area holds the sources.
  have hargs : ∀ i < slots sig, InRegions ((allocState bytes s).rd ++ (allocState bytes s).wr)
      (argAddr s i) 4 := fun i hi => by
    have hmem : (⟨argAddr s 0, 4 * slots sig⟩, wa) ∈ allRegions sig wa s := by
      simp [allRegions, show slots sig ≠ 0 by omega]
    have hc : (⟨argAddr s 0, 4 * slots sig⟩ : Region).Contains (argAddr s i) 4 := by
      show (⟨addr (s.gpr .esp) (4 + 4 * 0), 4 * slots sig⟩ : Region).Contains
        (addr (s.gpr .esp) (4 + 4 * i)) 4
      rw [addr_eq (x := s.gpr .esp) (k := 4 + 4 * 0) (by omega),
        addr_eq (x := s.gpr .esp) (k := 4 + 4 * i) (by omega)]
      exact Offset.contains _ (by omega) (by omega) (by omega)
    cases wa with
    | false =>
      refine ⟨_, List.mem_append_left _ ?_, hc⟩
      simp only [allocState_rd, hrd]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
    | true =>
      refine ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), hc⟩
      rw [hwr]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  -- The tag.
  have htb : ((⟨(arg s (tagSlot sig q)).setWidth 64, 16⟩ : Region), true) ∈
      Sig.bufs sig.params (stackArgs sig s) := by
    rw [hbO]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have htw : (⟨(arg s (tagSlot sig q)).setWidth 64, 16⟩ : Region) ∈ s.wr := by
    rw [hwr]
    exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_left _ htb, rfl⟩, rfl⟩
  have htd : (⟨(arg s (tagSlot sig q)).setWidth 64, 16⟩ : Region).Disjoint
      ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ := by
    rw [hsp]
    exact (Region.Disjoint.symm (hres _ hbelow _ (List.mem_append_left _ htb))).sub_right
      (Offset.sub_below _ (by omega) (by omega))
  have harg : (allocState bytes s).mem.readW (addr ((allocState bytes s).gpr .esp)
      (bytes + 4 + 4 * tagSlot sig q)) 32 = arg s (tagSlot sig q) := by
    rw [hesp, hsrc]; rfl
  obtain ⟨hrun, hrd', hwr', hg, hf, hv, hslot, hW⟩ := tagSetup_run (bytes := bytes) (n := slots sig)
    (j := tagSlot sig q) (u := allocState bytes s) (by rw [hesp, hE]; omega) hb hj
    (by rw [hesp]; exact List.mem_cons_self ..) (fun i hi => by rw [hesp, hsrc]; exact hargs i hi)
    (by rw [harg]; exact List.mem_cons_of_mem _ htw) (by rw [harg, hesp]; exact htd)
  rw [harg, hesp] at hrun hslot hW
  rw [hesp] at hf hv
  have hespN : (narrowT sig q nm e n bytes wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes := by
    rw [narrowT_gpr, hg _ (by decide) (by decide), hesp]
  have hargN : ∀ k < slots sig, arg (narrowT sig q nm e n bytes wa s) k =
      if k = tagSlot sig q then tagBuf sig bytes s else arg s k := fun k hk => by
    show (narrowT sig q nm e n bytes wa s).mem.readW
      (((narrowT sig q nm e n bytes wa s).gpr .esp + BitVec.ofNat 32 (4 + 4 * k)).setWidth 64) 32 = _
    rw [hespN, narrowT_mem]
    exact (hv k hk).trans (by rw [hsrc]; rfl)
  refine ⟨hrun, hrd', hwr', hespN, fun r h₁ h₂ h₃ => ?_, ?_, by rw [narrowT_mem]; exact hf,
    by rw [narrowT_mem]; exact hslot, fun i hi => ?_⟩
  · rw [narrowT_gpr, hg r h₁ h₂, allocState_gpr _ _ h₃]
  · rw [stackArgs_tagWork hq, stackArgs_congr hq (s' := s) fun k hk hk' => by
      rw [hargN k hk]; simp only [hk', ↓reduceIte], hargN _ hj]
    simp only [↓reduceIte]
    rfl
  · rw [narrowT_mem, show (tagBuf sig bytes s).setWidth 64 =
      (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 + BitVec.ofNat 64 (8 + 4 * slots sig) from
        addr_eq (by rw [hE]; omega)]
    exact hW i hi

theorem allRegions_narrowT (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) (hl : Sig.noLists sig.params = true) :
    allRegions (sig.tagWork q nm e n) wa (narrowT sig q nm e n bytes wa s) =
      innerRegions sig q nm e n bytes wa s := by
  obtain ⟨-, -, -, hespN, -, hargs, -⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb hs hl
  have h0 : slots sig ≠ 0 := by have := tagSlot_lt hq; omega
  simp only [allRegions, hargs, slots_tagWork hq, h0, ite_false, innerRegions, argAddr, hespN]

/-- The relation of `Sig.contract`'s disjointness is symmetric. -/
theorem disj_symm {x y : Region × Bool} (h : (x.2 || y.2) → x.1.Disjoint y.1) :
    (y.2 || x.2) → y.1.Disjoint x.1 :=
  fun hb => (h (by rw [Bool.or_comm]; exact hb)).symm

/-- The function's buffers lie below the reserved stack, outside the frame. -/
theorem bufs_out {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) (hb : 0 < bytes) :
    ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := by
  rw [pre_stack hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
        List Region) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  exact fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (below_sub' _ hx hk)

/-- The other buffers are the function's. -/
theorem other_bufs (hq : sig.params[q]? = some (nmT, .array true .u8 16)) (s : State) :
    ∀ b ∈ Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++
        Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1)),
      b ∈ Sig.bufs sig.params (stackArgs sig s) := fun b hb => by
  rw [(tag_bufs (nm := "") (e := .u8) (n := 0) hq s 0).1]
  rcases List.mem_append.mp hb with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- The tag lies outside the other buffers, and the code's memory agrees
with the function's on them and holds the tag in the buffer (`TagIn`). -/
theorem narrowT_tagIn (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) (hl : Sig.noLists sig.params = true) :
    TagIn (Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++
        Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1)))
      ((arg s (tagSlot sig q)).setWidth 64) ((tagBuf sig bytes s).setWidth 64) s.mem
      (narrowT sig q nm e n bytes wa s).mem ∧
    ∀ b ∈ Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++
        Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1)),
      b.1.Disjoint ⟨(arg s (tagSlot sig q)).setWidth 64, 16⟩ := by
  obtain ⟨-, -, -, -, -, -, hf, -, hW⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb hs hl
  have hout := bufs_out hs hl (by omega)
  have hB := other_bufs hq s
  obtain ⟨hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s 0
  rw [pre_stack hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, hpw, -, -, -⟩ := hs
  have harea : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 + 4 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) := by
    rw [Taint.sub_setWidth (by omega), Offset.sub_ofNat_eq _ (show bytes - 4 ≤ bytes by omega),
      Nat.sub_sub_self (by omega)]
    rfl
  refine ⟨⟨fun b hb x hx => (hf x fun r hr hc => ?_).symm, hW⟩, fun b hb => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    rw [harea] at hc
    exact hout b (hB b hb) (x := bytes - 4) (k := 4 * slots sig + 20) (by omega) (by omega) x hx hc
  · have hpw' := List.Pairwise.sublist (List.sublist_append_left _ _) hpw
    rw [hbO, List.pairwise_middle disj_symm] at hpw'
    exact (((List.pairwise_cons.mp hpw').1 b hb rfl)).symm

/-- The code's precondition holds in `narrowT`, from the function's. -/
theorem narrowT_pre (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes ∧ 8 + 4 * slots sig + n * e.size ≤ bytes)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pre (narrowT sig q nm e n bytes wa s) := by
  obtain ⟨-, -, -, hespN, -, hargs, -⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb.1 hs hl
  have hall := allRegions_narrowT (nm := nm) (e := e) (n := n) hq hb.1 hs hl
  have hin := narrowT_tagIn (nm := nm) (e := e) (n := n) (wa := wa) hq hb.1 hs hl
  have hout := bufs_out hs hl (by omega)
  have hB := other_bufs hq s
  obtain ⟨hbO, hbI⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s ((tagBuf sig bytes s).setWidth 64)
  rw [pre_stack hl] at hs
  obtain ⟨⟨hst, hfit⟩, -, -, hpw, -, hnw, hpr⟩ := hs
  have hscr : (tagBuf sig bytes s).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)) :=
    sub_add_setWidth (by omega) (by omega)
  have harea : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) := sub_add_setWidth (by omega) (by omega)
  have hsp : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes := Taint.sub_setWidth (by omega)
  have hpwB : (Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++
      Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1))).Pairwise
        (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) := by
    have hpw' := List.Pairwise.sublist (List.sublist_append_left _ _) hpw
    rw [hbO, List.pairwise_middle disj_symm] at hpw'
    exact (List.pairwise_cons.mp hpw').2
  have hWB : ∀ b ∈ Sig.bufs (sig.params.take q) (vals s (preWidths sig q) 0) ++
      Sig.bufs (sig.params.drop (q + 1)) (vals s (postWidths sig q) (tagSlot sig q + 1)),
      (⟨(tagBuf sig bytes s).setWidth 64, n * e.size⟩ : Region).Disjoint b.1 := fun b hb => by
    rw [hscr]; exact (hout b (hB b hb) (by omega) (by omega)).symm
  refine (pre_stack (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
    (Sig.noLists_tagWork _ _ _ hq hl)).mpr ?_
  rw [hall, hespN, hargs, slots_tagWork hq]
  refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [sub_toNat (by omega)]; omega
  · rw [sub_toNat (by omega)]; omega
  · -- Pairwise disjoint.
    rw [innerRegions, innerArgs, hbI, List.pairwise_append, List.pairwise_middle disj_symm]
    refine ⟨List.pairwise_cons.mpr ⟨fun b hb _ => hWB b hb, hpwB⟩, by simp, fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    rw [harea]
    rcases List.mem_append.mp ha with ha | ha
    · exact hout a (hB a (List.mem_append_left _ ha)) (by omega) (by omega)
    · rcases List.mem_cons.mp ha with rfl | ha
      · rw [hscr]
        exact below_disjoint _ (stack + bytes) (by omega) (by omega) (.inr (by omega)) (by omega) (by omega)
      · exact hout a (hB a (List.mem_append_right _ ha)) (by omega) (by omega)
  · -- The reserved stack: the frame's first word and the stack below it.
    intro r hr a ha
    rw [hsp] at hr
    simp only [List.mem_cons, stackBelow_sp'] at hr
    have hr' : r = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes, 4⟩ ∨
        (stack ≠ 0 ∧ r = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes + stack), stack⟩) := by
      rcases hr with rfl | hr
      · exact .inl rfl
      · by_cases h0 : stack = 0
        · simp [h0] at hr
        · simp only [h0, ite_false, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    have hframe : ∀ {x k : Nat}, x ≤ bytes - 4 → bytes - x + k ≤ bytes →
        r.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := fun h₁ h₂ => by
      rcases hr' with rfl | ⟨h0, rfl⟩
      · exact below_disjoint _ (stack + bytes) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
      · exact below_disjoint _ (stack + bytes) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
    have hbuf : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), r.Disjoint a.1 := fun a ha => by
      rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
      · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
    rw [innerRegions, innerArgs, hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hbuf a (hB a (List.mem_append_left _ ha))
      · rcases List.mem_cons.mp ha with rfl | ha
        · rw [hscr]; exact hframe (by omega) (by omega)
        · exact hbuf a (hB a (List.mem_append_right _ ha))
    · simp only [List.mem_singleton] at ha; subst ha
      rw [harea]; exact hframe (by omega) (by omega)
  · -- No buffer wraps around.
    intro a ha
    rw [innerArgs, hbI] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a (hB a (List.mem_append_left _ ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · show ((tagBuf sig bytes s).setWidth 64).toNat + n * e.size ≤ 2 ^ 32
        rw [hscr, toNat_sub64 (by simp; omega)]
        simp; omega
      · exact hnw a (hB a (List.mem_append_right _ ha))
  · -- The precondition.
    rw [stackArgs_split hq] at hpr
    exact ho.pre _ _ _ _ _ _ (vals_pre_length s) (vals_post_length s _) hin.1 hpr

end

/-! ## Public data -/

/-- What a contract's `leak` says of the values and memory of two runs:
nothing, if it has none. -/
def leakAgree {ws : List ArgWord} : Option (Curry ws (Mem → List Nat)) → List (BitVec 64) → Mem →
    List (BitVec 64) → Mem → Prop
  | none, _, _, _, _ => True
  | some f, vs₁, m₁, vs₂, m₂ => Curry.apply ws f vs₁ m₁ = Curry.apply ws f vs₂ m₂

/-- The public data of a contract, with every argument on the stack. -/
theorem pubL_stack {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.gpr .esp = s₂.gpr .esp ∧ leakAgree leak (stackArgs sig s₁) s₁.mem (stackArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((stackArgs sig s₁).getD i 0).setWidth ((widths sig).getD i 64) =
          ((stackArgs sig s₂).getD i 0).setWidth ((widths sig).getD i 64) := by
  simp only [Sig.contract]
  rw [args_stack]
  simp only [Sig.descs_of_noLists _ _ _ hl, List.not_mem_nil, false_implies, implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

theorem getD_middle {l₁ l₂ : List (BitVec 64)} {a b : BitVec 64} {i : Nat} (h : i ≠ l₁.length) :
    (l₁ ++ a :: l₂).getD i 0 = (l₁ ++ b :: l₂).getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i l₁.length with h' | h'
  · rw [List.getElem?_append_left h', List.getElem?_append_left h']
  · rw [List.getElem?_append_right h', List.getElem?_append_right h']
    obtain ⟨j, hj⟩ : ∃ j, i - l₁.length = j + 1 := ⟨i - l₁.length - 1, by omega⟩
    rw [hj, List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem getD_middle_self {l₁ l₂ : List (BitVec 64)} {a : BitVec 64} :
    (l₁ ++ a :: l₂).getD l₁.length 0 = a := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

section
variable {sig : Sig} {q : Nat} {nmT nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {wa : Bool} {stack bytes : Nat}

/-- The function's public data is the code's public data in `narrowT`. -/
theorem narrowT_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes)
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hl : Sig.noLists sig.params = true) :
    ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).pub
      (narrowT sig q nm e n bytes wa s₁) (narrowT sig q nm e n bytes wa s₂) := by
  rw [pubL_stack hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  obtain ⟨-, -, -, e₁, -, a₁, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb h₁ hl
  obtain ⟨-, -, -, e₂, -, a₂, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb h₂ hl
  obtain ⟨t₁, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) (wa := wa) hq hb h₁ hl
  obtain ⟨t₂, -⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) (wa := wa) hq hb h₂ hl
  have p₁ := ((pre_stack hl).mp h₁).2.2.2.2.2.2
  have p₂ := ((pre_stack hl).mp h₂).2.2.2.2.2.2
  rw [stackArgs_split hq] at p₁ p₂
  refine (pubL_stack (sig := sig.tagWork q nm e n) (pre := preI) (post := postI) (leak := leakI)
    (Sig.noLists_tagWork _ _ _ hq hl)).mpr ⟨⟨by rw [e₁, e₂, hsp], ?_⟩, fun i hi => ?_⟩
  · rw [a₁, a₂, innerArgs, innerArgs]
    rw [stackArgs_split hq, stackArgs_split hq] at hlk
    have hol := ho.leak
    revert hlk hol
    cases leak <;> cases leakI <;> simp only [leakAgree, imp_self, implies_true, false_implies]
    rename_i f g
    intro hlk hol
    rw [hol _ _ _ _ _ _ (vals_pre_length s₁) (vals_post_length s₁ _) t₁ p₁,
      hol _ _ _ _ _ _ (vals_pre_length s₂) (vals_post_length s₂ _) t₂ p₂]
    exact hlk
  · rw [Sig.pubs_tagWork _ _ _ hq] at hi
    rw [a₁, a₂, widths_tagWork hq, innerArgs, innerArgs]
    by_cases hik : i = (vals s₁ (preWidths sig q) 0).length
    · rw [hik, getD_middle_self, show (vals s₁ (preWidths sig q) 0).length =
        (vals s₂ (preWidths sig q) 0).length by rw [vals_length, vals_length], getD_middle_self]
      simp only [tagBuf, hsp]
    · have hik' : i ≠ (vals s₂ (preWidths sig q) 0).length := by
        rw [vals_length]; rw [vals_length] at hik; exact hik
      rw [getD_middle (b := (arg s₁ (tagSlot sig q)).setWidth 64) hik,
        getD_middle (b := (arg s₂ (tagSlot sig q)).setWidth 64) hik', ← stackArgs_split hq,
        ← stackArgs_split hq]
      exact hpa i hi

/-- The tag pointer is public. -/
theorem tag_pub (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa stack leak).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    arg s₁ (tagSlot sig q) = arg s₂ (tagSlot sig q) := by
  obtain ⟨-, hpa⟩ := (pubL_stack hl).mp hp
  have hk : (vals s₁ (preWidths sig q) 0).length = (Sig.psWords (sig.params.take q) abi.ptrBits).length :=
    vals_pre_length s₁
  have hpub : (sig.params.flatMap (·.2.pubs)).getD (vals s₁ (preWidths sig q) 0).length false = true := by
    conv => lhs; rw [Sig.params_split hq]
    rw [List.flatMap_append, List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Sig.pubs_length _ abi.ptrBits, hk]),
      Sig.pubs_length _ abi.ptrBits, hk, Nat.sub_self]
    rfl
  have hw : (widths sig).getD (vals s₁ (preWidths sig q) 0).length 64 = 32 := by
    rw [widths_split hq, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [vals_length]), vals_length, Nat.sub_self]
    rfl
  have h := hpa _ hpub
  rw [hw, stackArgs_split hq, stackArgs_split hq, getD_middle_self,
    show (vals s₁ (preWidths sig q) 0).length = (vals s₂ (preWidths sig q) 0).length by
      rw [vals_length, vals_length], getD_middle_self] at h
  simpa using h


/-! ## The run -/

/-- The addresses `tagOut n` accesses, from `esp = sp`, for the tag pointer `t`. -/
def tagOutTrace (n : Nat) (sp t : BitVec 32) : List Leak :=
  [.addr (addr sp (4 + 4 * n)), .addr (addr sp (8 + 4 * n)), .addr (t.setWidth 64)]

/-- The state after `tagOut n` from `u`, if it runs. -/
def tagOutState (n : Nat) (u : State) : State :=
  ((execBlock isa (tagOut n) u).map Prod.fst).getD u

/-- Every region of the code's contract is one of the function's buffers,
the working space, or the copy of the arguments. -/
theorem mem_innerRegions (hq : sig.params[q]? = some (nmT, .array true .u8 16)) {s : State}
    {a : Region × Bool} (ha : a ∈ innerRegions sig q nm e n bytes wa s) :
    a ∈ Sig.bufs sig.params (stackArgs sig s) ∨ a = (⟨(tagBuf sig bytes s).setWidth 64, n * e.size⟩, true) ∨
      a = (⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64, 4 * slots sig⟩, wa) := by
  have hB := other_bufs hq s
  obtain ⟨-, hbI⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s ((tagBuf sig bytes s).setWidth 64)
  rw [innerRegions, innerArgs, hbI] at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact .inl (hB a (List.mem_append_left _ ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact .inr (.inl rfl)
      · exact .inl (hB a (List.mem_append_right _ ha))
  · simp only [List.mem_singleton] at ha; exact .inr (.inr ha)

/-- A run of the code from `narrowT s` is a run of `withTagScratch` from
`s`, after `tagSetup`'s accesses and before `tagOut`'s, which keeps what the
calling convention requires, whose memory is the code's with the buffer's
first 16 bytes copied to the tag (`TagOut`), and whose result is the code's. -/
theorem withTagScratch_run {c : Prog isa} (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes ∧ 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧
      bytes % 4 = 0)
    (hsp : NoSp c) (hd : stackUse c ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowT sig q nm e n bytes wa s) t s₃)
    (ha : abiPreserved (narrowT sig q nm e n bytes wa s) s₃) (hl : Sig.noLists sig.params = true) :
    Exec isa (withTagScratch bytes (slots sig) (tagSlot sig q) c) s
        (tagSetupTrace bytes (slots sig) (tagSlot sig q) (s.gpr .esp - BitVec.ofNat 32 bytes)
            (arg s (tagSlot sig q)) ++
          (t ++ tagOutTrace (slots sig) (s.gpr .esp - BitVec.ofNat 32 bytes) (arg s (tagSlot sig q))))
        (popState bytes s (tagOutState (slots sig)
          (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))) ∧
      abiPreserved s (popState bytes s (tagOutState (slots sig)
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))) ∧
      TagOut ((arg s (tagSlot sig q)).setWidth 64) ((tagBuf sig bytes s).setWidth 64) s₃.mem
        (popState bytes s (tagOutState (slots sig)
          (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))).mem ∧
      (popState bytes s (tagOutState (slots sig)
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))).gpr .eax =
        s₃.gpr .eax ∧
      (popState bytes s (tagOutState (slots sig)
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))).gpr .edx =
        s₃.gpr .edx := by
  obtain ⟨hb24, hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', hespN, hg, -, hf, hslot, -⟩ :=
    narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb24 hs hl
  have hout := bufs_out hs hl (by omega)
  obtain ⟨hbO, -⟩ := tag_bufs (nm := nm) (e := e) (n := n) hq s 0
  rw [pre_stack hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hE : (s.gpr .esp - BitVec.ofNat 32 bytes).toNat = (s.gpr .esp).toNat - bytes := sub_toNat (by omega)
  have hsp64 : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes := Taint.sub_setWidth (by omega)
  generalize ht : arg s (tagSlot sig q) = tg at hrun hslot ⊢
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, show 0 < bytes by omega, hb1, hb2, show bytes ≤ (s.gpr .esp).toNat by omega,
      and_self, ite_true]
    rfl
  -- Addresses in the frame, as offsets below `esp`.
  have hoff : ∀ {d : Nat}, d ≤ bytes → (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 d).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - d) := fun h => sub_add_setWidth h (by omega)
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 a, k⟩]
        (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := fun ha hk =>
    Covers.one ⟨_, List.mem_cons_self .., by
      rw [hsp64]; exact Offset.contains_below _ ha hk (by omega)⟩
  have hbufR : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have htb : ((⟨tg.setWidth 64, 16⟩ : Region), true) ∈ Sig.bufs sig.params (stackArgs sig s) := by
    rw [hbO, ht]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- The code runs within the function's regions and the frame.
  have hcovW : Covers (((innerRegions sig q nm e n bytes wa s).filter (·.2)).map (·.1))
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hoff (by omega)]; exact hF (by omega) (by omega)
    · rw [hoff (by omega)]; exact hF (by omega) (by omega)
  have hcovR : Covers (((innerRegions sig q nm e n bytes wa s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    rcases mem_innerRegions hq ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (by rw [hoff (by omega)]; exact hF (by omega) (by omega))
  have hw := Exec.widen he (rd := s.rd)
    (wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrowT sig q nm e n bytes wa s).withRegions s.rd
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) =
      tagSetupState bytes (slots sig) (tagSlot sig q) (allocState bytes s) by
    rw [narrowT, State.withRegions_withRegions, ← allocState_rd bytes s, ← hrd',
      show ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr = (allocState bytes s).wr
        from rfl, ← hwr', State.withRegions_self]] at hw
  -- What the code writes: its writable regions, and the stack below `esp`.
  have hesp₃ : s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
    (ha.1 .esp (by simp [calleeSaved])).trans hespN
  have hfs := Exec.frameSp he hsp (by rw [hespN, hE]; omega)
  rw [hespN] at hfs
  have hcode : ∀ {R : Region}, (∀ a ∈ Sig.bufs sig.params (stackArgs sig s), R.Disjoint a.1) →
      R.Disjoint ⟨(tagBuf sig bytes s).setWidth 64, n * e.size⟩ →
      (wa = true → R.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64,
        4 * slots sig⟩) →
      R.Disjoint (below (s.gpr .esp - BitVec.ofNat 32 bytes) (stackUse c)) →
      ∀ r ∈ (narrowT sig q nm e n bytes wa s).wr ++
        [below (s.gpr .esp - BitVec.ofNat 32 bytes) (stackUse c)], R.Disjoint r := by
    intro R h₁ h₂ h₃ h₄ r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
      rcases mem_innerRegions hq ha with ha | rfl | rfl
      · exact h₁ a ha
      · exact h₂
      · exact h₃ hf'
    · simp only [List.mem_singleton] at hr; subst hr; exact h₄
  have hbelowc : below (s.gpr .esp - BitVec.ofNat 32 bytes) (stackUse c) =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes + stackUse c), stackUse c⟩ := by
    show (⟨(s.gpr .esp - BitVec.ofNat 32 bytes - BitVec.ofNat 32 (stackUse c)).setWidth 64, _⟩ : Region) = _
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Taint.sub_setWidth (by omega)]
  -- The saved tag pointer, which the code does not write.
  have hslot₃ : s₃.mem.readW (addr (s.gpr .esp - BitVec.ofNat 32 bytes) (4 + 4 * slots sig)) 32 = tg := by
    have hA : addr (s.gpr .esp - BitVec.ofNat 32 bytes) (4 + 4 * slots sig) =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (4 + 4 * slots sig)) := hoff (by omega)
    rw [hA] at hslot ⊢
    have d₁ : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s),
        (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (4 + 4 * slots sig)), 4⟩ : Region).Disjoint a.1 :=
      fun a ha => Region.Disjoint.symm (hout a ha (by omega) (by omega))
    have d₂ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (4 + 4 * slots sig)), 4⟩ : Region).Disjoint
        ⟨(tagBuf sig bytes s).setWidth 64, n * e.size⟩ := by
      rw [hoff (by omega)]
      exact below_disjoint _ (stack + bytes) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
    have d₃ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (4 + 4 * slots sig)), 4⟩ : Region).Disjoint
        ⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64, 4 * slots sig⟩ := by
      rw [hoff (by omega)]
      exact below_disjoint _ (stack + bytes) (by omega) (by omega) (.inr (by omega)) (by omega) (by omega)
    have d₄ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (4 + 4 * slots sig)), 4⟩ : Region).Disjoint
        (below (s.gpr .esp - BitVec.ofNat 32 bytes) (stackUse c)) := by
      rw [hbelowc]
      exact below_disjoint _ (stack + bytes) (by omega) (by omega) (.inr (by omega)) (by omega) (by omega)
    exact (hfs.readW (Region.contains_self _ _) (hcode d₁ d₂ (fun _ => d₃) d₄) (by decide)).trans hslot
  -- `tagOut`, with the function's regions and the frame.
  have e₃ : (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)).gpr
      .esp = s.gpr .esp - BitVec.ofNat 32 bytes := hesp₃
  have hfr : ∀ {d k : Nat}, d + k ≤ bytes → InRegions
      ((s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)).rd ++
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)).wr)
      (addr (s.gpr .esp - BitVec.ofNat 32 bytes) d) k := fun h =>
    ⟨_, List.mem_append_right _ (List.mem_cons_self ..), by
      rw [addr_eq (by rw [hE]; omega)]; exact Offset.contains_base _ h (by omega)⟩
  have htw : (⟨tg.setWidth 64, 16⟩ : Region) ∈ s.wr := hbufW _ htb rfl
  obtain ⟨u₄, hto, r₄, w₄, mem₄, g₄⟩ := tagOut_run (n := slots sig)
    (u := s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr))
    (by rw [e₃]; exact hfr (by omega)) (by rw [e₃]; exact hfr (by omega))
    (by rw [State.withRegions_mem, e₃, hslot₃]
        exact ⟨_, List.mem_cons_of_mem _ htw, Region.contains_self _ _⟩)
  rw [State.withRegions_mem, e₃, hslot₃] at hto
  rw [State.withRegions_mem, e₃] at mem₄
  have hst₄ : tagOutState (slots sig)
      (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)) = u₄ := by
    simp [tagOutState, hto]
  rw [hst₄]
  -- The pop.
  have hesp₄ : u₄.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes := (g₄ .esp (by decide)).trans e₃
  have hu₄ : u₄.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) = u₄ := by
    rw [show s.rd = u₄.rd from r₄.symm,
      show (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr : List Region) = u₄.wr
        from w₄.symm, State.withRegions_self]
  have hpop : isa.pop (.free bytes) (allocState bytes s) u₄ = some (popState bytes s u₄) := by
    rw [← hu₄]
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, allocState_esp, allocState_wr,
      hesp₄, List.head?_cons, show 0 < bytes by omega, hb1, hb2, and_self, ite_true, List.tail_cons,
      BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) (Exec.seq hw (Exec.block hto))) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  have hR : ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
      (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := fun hx hk =>
    (Offset.base_disjoint_below _ (n := stack + bytes) (k := 4) (by omega)).sub_right
      (below_sub' _ hx hk)
  have hmem₄ : u₄.mem = s₃.mem.writeW (tg.setWidth 64) (s₃.mem.readW ((tagBuf sig bytes s).setWidth 64) 128) := by
    rw [mem₄, tagOutMem, hslot₃]; rfl
  refine ⟨hex, ⟨fun r hr => ?_, ?_⟩, ⟨fun x hx => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · -- The callee-saved registers.
    simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : r = .esp
    · subst hqs; simp only [ite_true]
    · simp only [hqs, ite_false]
      have hqa : r ≠ .eax := fun h => by subst h; simp [calleeSaved] at hr
      have hqc : r ≠ .ecx := fun h => by subst h; simp [calleeSaved] at hr
      rw [g₄ r hqc, State.withRegions_gpr, ha.1 r hr, hg r hqa hqc hqs]
  · -- The return address: `tagOut` writes only the tag, the code its regions
    -- and below `esp`, and `tagSetup` only the frame.
    show u₄.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
    have f₄ : Frame [⟨tg.setWidth 64, 16⟩] s₃.mem u₄.mem := by
      rw [hmem₄]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have e₁ : u₄.mem.readW ((s.gpr .esp).setWidth 64) 32 = s₃.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
      f₄.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hres _ (List.mem_cons_self ..) (⟨tg.setWidth 64, 16⟩, true)
          (List.mem_append_left _ htb)) (by decide)
    have d₁ : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
        ⟨(tagBuf sig bytes s).setWidth 64, n * e.size⟩ := by
      rw [hoff (by omega)]; exact hR (by omega) (by omega)
    have d₂ : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
        ⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64, 4 * slots sig⟩ := by
      rw [hoff (by omega)]; exact hR (by omega) (by omega)
    have d₃ : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
        (below (s.gpr .esp - BitVec.ofNat 32 bytes) (stackUse c)) := by
      rw [hbelowc]; exact hR (by omega) (by omega)
    have e₂ : s₃.mem.readW ((s.gpr .esp).setWidth 64) 32 =
        (narrowT sig q nm e n bytes wa s).mem.readW ((s.gpr .esp).setWidth 64) 32 :=
      hfs.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _)
        (hcode (fun a ha => hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha)) d₁
          (fun _ => d₂) d₃) (by decide)
    have d₄ : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
        ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 + 4, 4 * slots sig + 20⟩ := by
      rw [show (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 + 4 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) by
          rw [hsp64, Offset.sub_ofNat_eq _ (show bytes - 4 ≤ bytes by omega), Nat.sub_sub_self (by omega)]
          rfl]
      exact hR (by omega) (by omega)
    have e₃ : (narrowT sig q nm e n bytes wa s).mem.readW ((s.gpr .esp).setWidth 64) 32 =
        s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
      hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d₄) (by decide)
    exact e₁.trans (e₂.trans e₃)
  · -- `TagOut`: the tag's bytes from the buffer, and nothing else written.
    show u₄.mem x = s₃.mem x
    rw [hmem₄]
    refine Mem.writeW128_apply_of_not fun h => hx ?_
    simp only [Region.Contains]; omega
  · show u₄.mem _ = _
    rw [hmem₄]
    exact Mem.writeW_readW128_apply _ _ _ _ hi
  · simp only [popState, State.setReg, State.withRegions_gpr, show Reg.eax ≠ Reg.esp by decide,
      ↓reduceIte]
    rw [g₄ .eax (by decide)]
    rfl
  · simp only [popState, State.setReg, State.withRegions_gpr, show Reg.edx ≠ Reg.esp by decide,
      ↓reduceIte]
    rw [g₄ .edx (by decide)]
    rfl


/-- Code verified for a function whose parameter `q` is working space that
also carries a 16-byte tag in its first 16 bytes (`Sig.tagWork`), with
`stack` bytes of stack, is verified for the function whose parameter `q` is
the tag, which allocates the working space in a frame of `bytes` more bytes
of stack (`withTagScratch`), if the two contracts are related by
`Sig.TagFrame`. -/
theorem Verified.tagScratch {c : Prog isa}
    {preI : Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → Prop)}
    {postI : (sig.tagWork q nm e n).Post abi.ptrBits}
    {leakI : Option (Curry ((sig.tagWork q nm e n).words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI))
    (ho : sig.TagFrame q nm e n abi.ptrBits pre post leak preI postI leakI)
    (hq : sig.params[q]? = some (nmT, .array true .u8 16))
    (hb : 24 + 4 * slots sig ≤ bytes ∧ 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧
      bytes % 4 = 0)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ stack)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withTagScratch bytes (slots sig) (tagSlot sig q) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hnsp : NoSp c := fun i hi => by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    simpa using hsp i hi
  -- Every run is `tagSetup`, the code's run from `narrowT`, and `tagOut`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrowT sig q nm e n bytes wa s) t s₃ ∧
      ((sig.tagWork q nm e n).contract abi preI postI wa stack leakI).post
        (narrowT sig q nm e n bytes wa s) s₃ ∧
      Exec isa (withTagScratch bytes (slots sig) (tagSlot sig q) c) s
        (tagSetupTrace bytes (slots sig) (tagSlot sig q) (s.gpr .esp - BitVec.ofNat 32 bytes)
            (arg s (tagSlot sig q)) ++
          (t ++ tagOutTrace (slots sig) (s.gpr .esp - BitVec.ofNat 32 bytes) (arg s (tagSlot sig q))))
        (popState bytes s (tagOutState (slots sig)
          (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))) ∧
      abiPreserved s (popState bytes s (tagOutState (slots sig)
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))) ∧
      TagOut ((arg s (tagSlot sig q)).setWidth 64) ((tagBuf sig bytes s).setWidth 64) s₃.mem
        (popState bytes s (tagOutState (slots sig)
          (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))).mem ∧
      (popState bytes s (tagOutState (slots sig)
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))).gpr .eax =
        s₃.gpr .eax ∧
      (popState bytes s (tagOutState (slots sig)
        (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)))).gpr .edx =
        s₃.gpr .edx := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq'⟩ := hcor _ (narrowT_pre hq ⟨hb.1, hb.2.1⟩ ho hs hl)
    exact ⟨t, s₃, he, hq', withTagScratch_run hq hb hnsp hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hpost, hex, ha, hto, heax, hedx⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stack]
    have hq' := (post_stack (sig := sig.tagWork q nm e n) (pre := preI) (post := postI)
      (leak := leakI)).mp hpost
    obtain ⟨-, -, -, -, -, hargs, -⟩ := narrowT_facts (nm := nm) (e := e) (n := n) (wa := wa) hq hb.1 hs hl
    obtain ⟨hin, hdis⟩ := narrowT_tagIn (nm := nm) (e := e) (n := n) (wa := wa) hq hb.1 hs hl
    have hpr := ((pre_stack hl).mp hs).2.2.2.2.2.2
    rw [stackArgs_split hq] at hpr
    rw [hargs, innerArgs] at hq'
    rw [heax, hedx, stackArgs_split hq]
    exact ho.post _ _ _ _ _ _ _ _ _ (vals_pre_length s) (vals_post_length s _) hin hpr hdis hto hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_stack hl).mp hp).1.1, tag_pub hq hp hl,
      hct _ _ _ _ _ _ (narrowT_pre hq ⟨hb.1, hb.2.1⟩ ho h₁ hl) (narrowT_pre hq ⟨hb.1, hb.2.1⟩ ho h₂ hl)
        (narrowT_pub hq hb.1 ho h₁ h₂ hp hl) f₁ f₂]

end

/-- `withTagScratch` writes `esp` only in its frame if its code does. -/
theorem withTagScratch_spSafe {bytes n j : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withTagScratch bytes n j c).all (fun i => !isa.writesSp i) = true := by
  have hc : ((List.range n).flatMap (copyArg bytes)).all (fun i => !isa.writesSp i) = true :=
    List.all_eq_true.mpr fun i hi => by
      obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hi
      simp only [copyArg, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rfl
  simp only [withTagScratch, tagSetup, Code.all, List.all_append, h, hc, Bool.true_and]
  rfl

end VG.X86
