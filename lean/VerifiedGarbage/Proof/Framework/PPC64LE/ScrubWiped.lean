module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# Returning without secret residue, for code that wipes its own frame (PPC64LE)

Code run by `withStackScratchWiped bytes r words c` (`Impl/StackScratch/PPC64LE.lean`)
zeroes its scratch buffer itself before it releases its frame. When the
wipe covers the whole of the frame's region (`8 * words = bytes - 32`) and
`c` has no frames of its own, nothing it wrote is left on the stack: two
runs of it with the same trace end with memories that agree outside the
buffers (`Exec.agreeWiped`). So it returns without secret residue followed
only by the clearing of the volatile registers it may write,
`scrubTail rb [] cl`, which wipes no stack (`Verified.scrubOf` with no
levels; `PPC64LE.Scrub.verifiedScrubbedWiped`).

Inside the frame, the two runs agree outside the buffers and the frame's
region (`Exec.agree`); the wipe then zeroes the region in both; and the
frame's release keeps what agrees (`pop_agr`), its header holding the back
chain, the stack pointer, in both.
-/

@[expose] public section

open VG.Impl.Scrub.PPC64LE VG.Impl.StackScratch.PPC64LE

namespace VG.PPC64LE.Scrub

/-- `wipeStores words` zeroes the `8 * words` bytes at `r12`, within a
writable region `⟨r12, B⟩`, with `r11` zero. -/
theorem wipeStores_zero (u : State) (B : Nat) (hB : B < 4096) (hqB : (u.gpr .r12).toNat + B ≤ 2 ^ 64)
    (hR : ⟨u.gpr .r12, B⟩ ∈ u.wr) (h0 : u.gpr .r11 = 0) :
    ∀ w, 8 * w ≤ B → execBlock isa (wipeStores w) u =
      some ({ u with mem := zeroOn (u.gpr .r12) 0 (8 * w) u.mem }, wipeTrace (u.gpr .r12) w)
  | 0, _ => by
    have hz : zeroOn (u.gpr .r12) 0 (8 * 0) u.mem = u.mem := by
      funext x; simp only [zeroOn, Nat.mul_zero]; split
      · next h => omega_using [h.1, h.2]
      · rfl
    rw [hz]; rfl
  | w + 1, hw => by
    rw [wipeStores_succ, execBlock_append, wipeStores_zero u B hB hqB hR h0 w (by omega_using [hw])]
    have hlt : (u.gpr .r12).toNat + 8 * w < 2 ^ 64 := by omega_using [hw, hqB]
    have hc : InRegions ({ u with mem := zeroOn (u.gpr .r12) 0 (8 * w) u.mem } : State).wr
        (({ u with mem := zeroOn (u.gpr .r12) 0 (8 * w) u.mem } : State).gpr .r12 + BitVec.ofNat 64 (8 * w)) 8 := by
      refine ⟨_, hR, ?_⟩
      simp only [Region.Contains]
      rw [show u.gpr .r12 + BitVec.ofNat 64 (8 * w) - u.gpr .r12 = BitVec.ofNat 64 (8 * w) by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlt])]
      omega_using [hw]
    simp only [Option.bind_some, execBlock, isa, exec_store_d (show Reg.r12 ≠ .r0 by decide)
      ⟨by omega_using [hw, hB], by omega_using []⟩ hc, Option.map_some, addrs, List.map_cons,
      List.map_nil, List.append_nil, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · congr 1
      funext x
      have e := off_lt x (u.gpr .r12) (8 * w) 8 (by omega_using [hw, hB])
      simp only [zeroOn, Mem.writeW, Mem.write, h0, Nat.reduceDiv, Nat.reduceMul] at e ⊢
      generalize (x - (_ + BitVec.ofNat 64 (8 * w))).toNat = r at e ⊢
      generalize (x - _).toNat = d at e ⊢
      repeat' split
      all_goals first | (exfalso; omega) | rfl | (simp; done)
    · simp only [wipeTrace, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- `wipe words` from a state whose frame region `⟨sp + 32, B⟩` it may write:
it zeroes the `8 * words` bytes at `sp + 32`. -/
theorem wipe_zero {u u' : State} {t : List Leak} {B words : Nat} (hB : B < 4096) (hw : 8 * words ≤ B)
    (hqB : (u.sp + 32).toNat + B ≤ 2 ^ 64) (hR : ⟨u.sp + 32, B⟩ ∈ u.wr)
    (h : execBlock isa (Impl.StackScratch.PPC64LE.wipe words) u = some (u', t)) :
    u'.mem = zeroOn (u.sp + 32) 0 (8 * words) u.mem := by
  have h12 : ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)).gpr .r12 =
      u.sp + 32 := by
    simp [State.write]
  have h11 : ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)).gpr .r11 = 0 := by
    simp [State.write]
  have he := wipeStores_zero ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)) B hB
    (by rw [h12]; exact hqB) (by simpa [State.write] using hR) h11 words hw
  have e : execBlock isa (Impl.StackScratch.PPC64LE.wipe words) u =
      some ({ ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)) with
        mem := zeroOn (u.sp + 32) 0 (8 * words) u.mem }, wipeTrace (u.sp + 32) words) := by
    simp only [Impl.StackScratch.PPC64LE.wipe, execBlock, isa, exec, show (32 : Nat) < 2 ^ 15 by decide,
      show (0 : Nat) < 2 ^ 15 by decide, ↓reduceIte]
    rw [show ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0 : BitVec 64)) =
        ((u.write .r12 (u.sp + BitVec.ofNat 64 32)).write .r11 (BitVec.ofNat 64 0)) from rfl]
    simp only [Option.map_some, he, h12, addrs, List.map_nil, List.nil_append]
    rfl
  rw [e] at h
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
  rfl

/-- Code without indirect calls or frames of its own, run by
`withStackScratchWiped` with a wipe of the whole of its frame's region: two
runs of it from states with the same stack pointer, writable regions and
unknowns, whose memories agree outside the regions `R`, and with the same
trace, end with the same unknowns and memories that agree outside `R`. -/
theorem Exec.agreeWiped {R : List Region} {B w : Nat} {r : Reg} {body : Prog isa}
    (hB : 32 < B ∧ B < 4096 ∧ B % 16 = 0) (hw : 8 * w = B - 32) (hic : icallFree body = true)
    (hd : body.ppc64leDepth = 0) {s₁ s₂ u₁ u₂ : State} {t₁ t₂ : List Leak}
    (e₁ : Exec isa (withStackScratchWiped B r w body) s₁ t₁ u₁)
    (e₂ : Exec isa (withStackScratchWiped B r w body) s₂ t₂ u₂)
    (hsp : s₁.sp = s₂.sp) (hwr : s₁.wr = s₂.wr) (hu : s₁.unknowns = s₂.unknowns)
    (hwrR : ∀ q ∈ s₁.wr, q ∈ R) (hBs : B ≤ s₁.sp.toNat)
    (hA : ∀ x, (∀ q ∈ R, ¬ q.Contains x 1) → s₁.mem x = s₂.mem x) (ht : t₁ = t₂) :
    u₁.unknowns = u₂.unknowns ∧ ∀ x, (∀ q ∈ R, ¬ q.Contains x 1) → u₁.mem x = u₂.mem x := by
  have hp := s₁.sp.isLt
  have hL : (s₁.sp - BitVec.ofNat 64 B).toNat = s₁.sp.toNat - B := toNat_sub_ofNat _ _ hBs
  -- The stack the frame's region covers.
  generalize hLd : s₁.sp - BitVec.ofNat 64 B = L at hL
  unfold withStackScratchWiped withStackScratch at e₁ e₂
  cases e₁ with | @frame _ _ _ _ f₁ y₁ _ tb₁ hp₁ b₁ hq₁ =>
  cases e₂ with | @frame _ _ _ _ f₂ y₂ _ tb₂ hp₂ b₂ hq₂ =>
  have hAg : Agr R L s₁.sp s₁.mem s₂.mem := fun x hx _ => hA x hx
  obtain ⟨sp₁, w₁, uk₁, hA₁, hsp₁, f, hwf, hf⟩ :=
    push_agr (L := L) (T := s₁.sp) hp₁ hp₂ hsp hwr hu hAg (by simp only [frameBytes]; omega_using [hL, hBs])
      (Nat.le_refl _)
  have hspf : f₁.sp = s₁.sp - BitVec.ofNat 64 B := by simpa [frameBytes] using hsp₁
  have hfT : f₁.sp.toNat = s₁.sp.toNat - B := by rw [hspf, hLd]; exact hL
  -- The frame's body: its trace is the same in both runs.
  have ht' : tb₁ = tb₂ := by
    simp only [addrs, hsp, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_nil, List.cons.injEq, true_and] at ht
    exact ht
  have hwrf : WrOk R L s₁.sp f₁.wr := by
    rw [hwf]; intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact .inr hf
    · exact .inl (hwrR q hq)
  obtain ⟨-, hU, hAy⟩ := Exec.agree (R := R) (L := L) (T := s₁.sp) b₁
    (by simp [icallFree, hic]) [] [] b₂ sp₁ w₁ uk₁ hwrf
    (by simp only [Code.ppc64leDepth, hd]; omega_using [hfT, hL, hBs])
    (by omega_using [hfT]) hA₁ (by rw [List.append_nil, List.append_nil, ht'])
  -- The wipe leaves the frame's region zero in each run.
  have hzero : ∀ {f y : State} {tb : List Leak},
      Exec isa (.seq (.block [.addSp r 32]) (.seq body (.block (Impl.StackScratch.PPC64LE.wipe w)))) f tb y →
      f.sp = s₁.sp - BitVec.ofNat 64 B → ⟨f.sp + 32, B - 32⟩ ∈ f.wr →
      ∀ x, InZ L s₁.sp x → y.mem x = 0 := by
    intro f y tb e hfs hfr x hx
    cases e with | seq a e' =>
    cases e' with | seq a' e'' =>
    cases e'' with | block hwp =>
    rename_i v₁ _ _ v₂ _ _
    obtain ⟨-, wv₁, pv₁⟩ := Exec.rdwr a
    obtain ⟨-, wv₂, pv₂⟩ := Exec.rdwr a'
    have hv2 : v₂.sp = f.sp := pv₂.trans pv₁
    have hm := wipe_zero (u := v₂) (B := B - 32) (words := w) (by omega_using [hB])
      (by omega_using [hw]) (by
        rw [hv2, show (32 : Addr) = BitVec.ofNat 64 32 from rfl, toNat_add_ofNat _ _ (by
          rw [hfs, hLd]; omega_using [hL, hBs, hp, hB])]
        rw [hfs, hLd, hL]; omega_using [hBs, hp, hB])
      (by rw [wv₂, wv₁, hv2]; exact hfr) hwp
    rw [hm]
    simp only [zeroOn]
    have hq : (v₂.sp + 32).toNat = s₁.sp.toNat - B + 32 := by
      rw [hv2, hfs, hLd, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        toNat_add_ofNat _ _ (by omega_using [hL, hBs, hp, hB]), hL]
    have := (sub_lt_iff (a := v₂.sp + 32) (x := x) (n := 8 * w) (by omega_using [hq, hw, hBs, hp, hB])).mpr
      (by simp only [InZ, hL] at hx; omega_using [hx.1, hx.2, hq, hw, hBs, hB])
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Nat.zero_le _, this⟩)]
  have hfr₁ : ⟨f₁.sp + 32, B - 32⟩ ∈ f₁.wr := by
    simp only [isa, push] at hp₁; split at hp₁ <;> [skip; cases hp₁]; cases hp₁; exact List.mem_cons_self
  have hfr₂ : ⟨f₂.sp + 32, B - 32⟩ ∈ f₂.wr := by
    simp only [isa, push] at hp₂; split at hp₂ <;> [skip; cases hp₂]; cases hp₂; exact List.mem_cons_self
  have hz₁ := hzero b₁ hspf hfr₁
  have hz₂ := hzero b₂ (by rw [← sp₁, hspf]) hfr₂
  -- So the two runs agree on every byte outside `R` before the frame's release.
  have hAll : Agr R s₁.sp s₁.sp y₁.mem y₂.mem := by
    intro x hx _
    by_cases hz : InZ L s₁.sp x
    · rw [hz₁ x hz, hz₂ x hz]
    · exact hAy x hx hz
  obtain ⟨-, -, py₁⟩ := Exec.rdwr b₁
  obtain ⟨-, -, py₂⟩ := Exec.rdwr b₂
  obtain ⟨q₁, q₂, hA'⟩ := pop_agr hq₁ hq₂ (by rw [py₁, py₂, sp₁]) hU hAll
  refine ⟨by rw [q₁, q₂, hU], fun x hx => hA' x hx ?_⟩
  simp only [InZ]; omega_using []

/-- What `verifiedScrubbedWiped` needs of a function's code: that it is
`withStackScratchWiped bytes r words body`, with a wipe of the whole of the
frame's region and a body without indirect calls or frames, within the
contract's stack. -/
structure WipedShape (code : Prog isa) (stack : Nat) where
  bytes : Nat
  reg : Reg
  words : Nat
  body : Prog isa
  code_eq : code = withStackScratchWiped bytes reg words body
  hB : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0
  hw : 8 * words = bytes - 32
  hic : icallFree body = true
  hd : body.ppc64leDepth = 0
  hs : bytes ≤ stack

/-- Two runs of such code from states that agree outside the buffers end
with the same unknowns and memories that agree outside them, as
`Verified.scrubOf` asks with no stack wiped. -/
theorem WipedShape.agree {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hA : ScrubAbi A) (h : Verified target c (sig.contract A pre post wa stack leak))
    (sh : WipedShape c stack) :
    ∀ s₁ s₂ t₁ t₂ u₁ u₂, (sig.contract A pre post wa stack leak).pre s₁ →
      (sig.contract A pre post wa stack leak).pre s₂ → (sig.contract A pre post wa stack leak).pub s₁ s₂ →
      Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns → Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
      u₁.unknowns = u₂.unknowns ∧
        ∀ x, (∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1) → ¬ Cover [] s₁.sp x → u₁.mem x = u₂.mem x := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hun a₁ a₂
  have ht := h.2.1 _ _ _ _ _ _ h₁ h₂ hp a₁ a₂
  have hBs : sh.bytes ≤ s₁.sp.toNat := by
    have := sh.hB.1
    rcases (contract_pre_scrub hA h₁).1 with h0 | h0
    · have := sh.hs; omega_using [h0, this, sh.hB.1]
    · have := sh.hs; omega_using [h0, this]
  obtain ⟨-, hwr, -, -, -, -, hsp, -, hm⟩ := ho
  rw [sh.code_eq] at a₁ a₂
  obtain ⟨hU, hM⟩ := Exec.agreeWiped (R := s₁.rd ++ s₁.wr) sh.hB sh.hw sh.hic sh.hd a₁ a₂ hsp hwr hun
    (fun q hq => List.mem_append_right _ hq) hBs hm ht
  exact ⟨hU, fun x hx _ => hM x hx⟩

end VG.PPC64LE.Scrub
