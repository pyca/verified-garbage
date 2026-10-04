import VerifiedGarbage.Proof.Aes.AArch64.Ecb
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# AES on whole blocks on AArch64: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt4` and `decrypt4`, and are proven at once, for any transformation of
four blocks with `CryptOk`: the prologue moves the arguments where
`vg_aes_ctr32` has them, saves the callee-saved registers and bitslices the
round keys as `vg_aes_ctr32`'s does (`Ctr32.lean`, `Group.lean`); the
groups (`Ecb.lean`) do the rest; the epilogue restores the registers.
-/

namespace VG.Proof.Aes

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and `data` may not wrap around the end of
the address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n`
are public; the key schedule and the data are secret. -/
def blocksAArch64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 2048⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).map
        (f (s.gpr .x1).toNat (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

theorem blocksSetup_ok (s : State) :
    ∃ s', runBlock isa blocksSetup s = some s' ∧ s'.gpr .x5 = s.gpr .x4 ∧ s'.gpr .x4 = s.gpr .x3 ∧
      s'.gpr .x3 = s.gpr .x2 ∧ (∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by rw [blocksSetup, movR, movR, movR, runBlock_cons, exec_addImm_x (by decide),
    runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
    exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    by simp [State.write, State.read], fun r h1 h2 h3 => by simp [State.write, h1, h2, h3],
    rfl, rfl, rfl, rfl⟩

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (show 16 * j + t < 16 * n by omega),
    show (16 * j + t) / 16 = j by omega, show (16 * j + t) % 16 = t by omega, getD_eq _ ht]

theorem correct_blocks {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt4 f) {s₀ : State} (hp : (Proof.Aes.blocksAArch64 f).pre s₀) :
    WP isa (blocks crypt4) s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksAArch64 f).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, hwrap, hR⟩ := hp
  have hwD : (⟨s₀.gpr .x2, 16 * (s₀.gpr .x3).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .x4, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .x0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  let n := (s₀.gpr .x3).toNat
  have n16 : 16 * n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .x4) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .x4 - s₀.gpr .x2).isLt
    omega
  have hR14 : (s₀.gpr .x1).toNat ≤ 14 := by omega
  let b := s₀.gpr .x4
  let D := s₀.gpr .x2
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, x5₁, x4₁, x3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := blocksSetup_ok s₀
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  refine WP.mono (save_ok (b := b) (wr₁ ▸ hwS) x5₁ (by decide)) fun s₂ ⟨sv₂, g₂, rd₂, wr₂, f₂⟩ => ?_
  obtain ⟨s₃, h₃, x2₃, x0₃, x1₃, o₃, m₃, rd₃, wr₃⟩ := keySetup_ok s₂
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have g₃ : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
      s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [o₃ r h1 h2 h3 h7, g₂, o₁ r h4 h5 h6]
  have hb₃ : s₃.gpr sb = b := by
    rw [o₃ sb (by decide) (by decide) (by decide) (by decide), g₂]; exact x5₁
  have f₀₃ : Frame [⟨b, 2048⟩] s₀.mem s₃.mem := by
    rw [m₃, ← m₁]
    exact f₂.sub fun r hr => ⟨⟨b, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  let R := (s₀.gpr .x1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .x0) (16 * (R + 1))
  have hk : KSetup s₃ b (s₀.gpr .x0) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .x0, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dSS }
  have hi₃ : KInv s₃ b (s₀.gpr .x0) R w R s₃ :=
    { hj := Nat.le_refl _
      x2 := by
        rw [x2₃, g₂, o₁ .x1 (by decide) (by decide) (by decide)]
        exact Offset.add_one_eq _
      x0 := by
        rw [x0₃, g₂, o₁ .x0 (by decide) (by decide) (by decide), o₁ .x1 (by decide) (by decide)
          (by decide), shl4]
      x1 := by rw [x1₃, g₂, show sb = .x5 from rfl, x5₁]; simp [keyAddr, b]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  obtain ⟨s₅, h₅, x0₅, o₅, m₅, rd₅, wr₅⟩ := keyDone_ok s₄
  refine WP.of_runBlock ⟨s₅, h₅, ?_⟩
  have g₅ : ∀ r ∈ [Reg.x3, .x4, .x5], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [o₅ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have x4₅ : s₅.gpr .x4 = s₀.gpr .x3 := by
    rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide) (by decide), g₂]; exact x4₁
  have x3₅ : s₅.gpr .x3 = D := by
    rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide) (by decide), g₂]; exact x3₁
  have hb₅ : s₅.gpr sb = b := by rw [show sb = .x5 from rfl, g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .x0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [x0₅, d₄.x1]; simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have fK : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₃.mem s₅.mem :=
    m₅ ▸ d₄.frame
  have hs : ESetup s₅ b D n R w :=
    { scr := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [m₅, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega] }
  have data₅ : EcbInv s₀.mem s₅.mem D n 0 (ecbOut f s₀.mem D R w) := by
    refine ecbInv_frame fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dDS.sub_right (scr_sub _ (by omega))) n16
      (ecbInv_frame f₀₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
        n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₅ b D n R w) ?_ fun s₆ gd => ?_)
  · refine WP.ite (s₀.gpr .x3 == 0) (by simp [AArch64.eval, State.read, x4₅]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by simp only [beq_iff_eq] at h0; simp [n, h0]
      exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine ecbGroups_ok hcr hs ⟨by omega, ?_, ?_, hb₅, hK0, rfl, rfl, rfl, Frame.refl _ _, data₅⟩
      · rw [x3₅]; simp
      · rw [x4₅]; simp [n]
  -- The epilogue.
  have sv : Saved s₀ b s₆.mem := by
    have sv₁ : Saved s₀ b s₂.mem := fun i hi => by
      rw [sv₂ i hi]
      exact o₁ _ (by revert i; decide) (by revert i; decide) (by revert i; decide)
    refine saved_frame (saved_frame (m₃ ▸ sv₁) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · intro r hr
      simp only [eRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (scr_disj _ (by omega) (by omega)).symm
      · exact (dDS.sub_right (scr_sub _ (by omega))).symm
  refine WP.mono (restore_ok (by rw [gd.wr, wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base (by decide) sv)
    fun s₇ ⟨rg₇, fR⟩ => ⟨rg₇, ?_⟩
  have dR : ∀ r ∈ [(⟨b, 8 * 59⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dDS.sub_right (Region.sub_prefix (by omega))
  show Spec.Aes.statesAt s₇.mem D n = _
  rw [statesAt_of_ecbInv (ecbInv_frame fR dR n16 gd.data)]
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

/-! ## The two functions -/

theorem blocks_correct {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt4 f)
    (hx30 : (blocks crypt4).allInstrs (fun i => [Reg.x30].all fun r => dstOf i != some r) = true)
    (hnc : (blocks crypt4).noCalls = true)
    (hv : (blocks crypt4).allInstrs keepsV = true)
    (s : State) (hs : (Proof.Aes.blocksAArch64 f).pre s) :
    ∃ t s', Exec isa (blocks crypt4) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 f).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (correct_blocks hcr hs) hx30 hnc
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' :=
  blocks_correct encrypt4_cryptOk (by decide +kernel) (by decide +kernel) (by decide +kernel) s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' :=
  blocks_correct decrypt4_cryptOk (by decide +kernel) (by decide +kernel) (by decide +kernel) s hs

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified AArch64.target encryptBlocks (Spec.Aes.encryptBlocksContract AArch64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified AArch64.target decryptBlocks (Spec.Aes.decryptBlocksContract AArch64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.Aes.AArch64
