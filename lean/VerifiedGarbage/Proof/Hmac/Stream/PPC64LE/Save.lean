module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Framework.Offset

/-!
# HMAC over any streaming hash function on PPC64LE: saving `r20`–`r25`

Our variables live in `r20`–`r25`, which none of the functions we call
writes: the streaming functions save and restore `r26`–`r31` (and SHA-2's
`r14`–`r19`), and a register restored from memory is secret to the analysis
of constant time, so it may not be an address after a call. We save our
caller's `r20`–`r25` at `scratch + so` (`Hash.saveAt`) and restore them from
there (`Hash.restoreAt`), as the streaming code does `r26`–`r31`
(`Proof/MdStream/PPC64LE/Basic.lean`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_std wp_ld contains_offset readW_writeW_save_so
  readW_writeW_save_so_l)

section
variable (so : Nat)

/-- The caller's nonvolatile registers `g` are saved in the scratch space at `b`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ Hash.savedAt so, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The memory after saving `r26`–`r31` (values `g`) at `b + so …`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 so) (g .r20)).writeW (b + BitVec.ofNat 64 (so + 8)) (g .r21)).writeW
    (b + BitVec.ofNat 64 (so + 16)) (g .r22)).writeW (b + BitVec.ofNat 64 (so + 24)) (g .r23)).writeW
    (b + BitVec.ofNat 64 (so + 32)) (g .r24)).writeW (b + BitVec.ofNat 64 (so + 40)) (g .r25)

theorem saveAt_eq (b : Reg) : Hash.saveAt so b = [.store .d .r20 b so, .store .d .r21 b (so + 8),
    .store .d .r22 b (so + 16), .store .d .r23 b (so + 24), .store .d .r24 b (so + 32),
    .store .d .r25 b (so + 40)] := rfl

theorem restoreAt_eq : Hash.restoreAt so = [.load .d .r20 .r21 so, .load .d .r22 .r21 (so + 16),
    .load .d .r23 .r21 (so + 24), .load .d .r24 .r21 (so + 32), .load .d .r25 .r21 (so + 40),
    .load .d .r21 .r21 (so + 8)] := rfl

end

section
variable {so : Nat}

theorem saveMem_saved (hso : so % 8 = 0 ∧ so ≤ 1024) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Saved so b g (saveMem so m b g) := by
  have := hso
  intro p hp
  simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saveMem, Mem.readW_writeW_self64,
    readW_writeW_save_so this.2, readW_writeW_save_so_l this.2]

theorem saveMem_frame (hso : so % 8 = 0 ∧ so ≤ 1024) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, so + 48⟩] m (saveMem so m b g) := by
  have := hso
  have c : ∀ d : Nat, d + 8 ≤ so + 48 → (⟨b, so + 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => contains_offset hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))).writeW (List.mem_singleton_self _) _
    (c _ (by omega))).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c _ (by omega))

/-- The saved registers are outside the part of the scratch space the
streaming code uses. -/
theorem saved_offset {p : Reg × Nat} (hp : p ∈ Hash.savedAt so) : so ≤ p.2 ∧ p.2 + 8 ≤ so + 48 := by
  simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- Saving `r26`–`r31` with the scratch pointer in `b`. -/
theorem save_ok (hso : so % 8 = 0 ∧ so ≤ 1024) {b : Reg} (hb : b ≠ .r0) {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, so ≤ d → d + 8 ≤ so + 48 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem so s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (Hash.saveAt so b ++ rest)) s Q := by
  have := hso
  rw [saveAt_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_std (by omega) rfl (hin _ (by omega) (by omega)) (fun s₁ g₁ => ?_) hb
  refine wp_std (by omega) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin _ (by omega) (by omega))
    (fun s₂ g₂ => ?_) hb
  refine wp_std (by omega) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₃ g₃ => ?_) hb
  refine wp_std (by omega) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₄ g₄ => ?_) hb
  refine wp_std (by omega) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₅ g₅ => ?_) hb
  refine wp_std (by omega) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₆ g₆ => ?_) hb
  refine k s₆ (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp]) ?_
  rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  simp only [saveMem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]

/-- Restoring `r26`–`r31` from the save area at `scr`. -/
theorem restore_ok (hso : so % 8 = 0 ∧ so ≤ 1024) {s : State} {scr : Addr} (h21 : s.gpr .r21 = scr)
    (hin : ∀ d, so ≤ d → d + 8 ≤ so + 48 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved so scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ Hash.savedAt so, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ (Hash.savedAt so).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (Hash.restoreAt so)) s Q := by
  have := hso
  have v : ∀ r d, (r, d) ∈ Hash.savedAt so → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  rw [restoreAt_eq]
  refine wp_ld (by omega) (by rw [h21]) (hin _ (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ld (by omega) (by rw [u₁.other _ (by decide), h21])
    (by rw [u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h21])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h21])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ld (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h21])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ld (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h21])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin _ (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .r20 _ (by simp [Hash.savedAt])]
    · rw [u₆.gpr, m5, v .r21 _ (by simp [Hash.savedAt])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .r22 _ (by simp [Hash.savedAt])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .r23 _ (by simp [Hash.savedAt])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .r24 _ (by simp [Hash.savedAt])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .r25 _ (by simp [Hash.savedAt])]
  · simp only [Hash.savedAt, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

end

/-- The nonvolatile registers our own code never writes: only the
streaming code may, and it restores them. -/
def untouched : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31]

theorem untouched_pres : ∀ r ∈ untouched, r ∈ preserved := by decide

/-- The nonvolatile registers are the caller's again once `restore` has run
and `untouched` hold their values. -/
theorem preserved_of {so : Nat} {s₀ s' : State} (hsv : ∀ p ∈ Hash.savedAt so, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ [Reg.r20, .r21, .r22, .r23, .r24, .r25] := by decide
  rcases key r hr with h | h
  · exact hu r h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.r20, so) (by simp [Hash.savedAt])
    · exact hsv (.r21, so + 8) (by simp [Hash.savedAt])
    · exact hsv (.r22, so + 16) (by simp [Hash.savedAt])
    · exact hsv (.r23, so + 24) (by simp [Hash.savedAt])
    · exact hsv (.r24, so + 32) (by simp [Hash.savedAt])
    · exact hsv (.r25, so + 40) (by simp [Hash.savedAt])

/-- Our caller's registers saved at `b + so` survive writes outside them. -/
theorem saved_keep {so : Nat} {b : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved so b g m)
    {rs : List Region} (hf : Frame rs m m')
    (hdis : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 so, 48⟩ r) : Saved so b g m' := by
  intro p hp
  rw [← h p hp]
  have ho := saved_offset hp
  refine hf.readW (r := ⟨b + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  exact (hdis r hr).sub_left (Offset.sub b ho.1 ho.2)

end VG.Proof.Hmac.Stream.PPC64LE
