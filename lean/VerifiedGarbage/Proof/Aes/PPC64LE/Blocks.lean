module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Ecb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Ecb
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Aes.PPC64LE.Keys
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Keys

/-!
# AES on whole blocks on PPC64LE: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt4` and `decrypt4`, and are proven at once, for any transformation of
four blocks with `CryptOk`: the prologue moves the scratch buffer, the count
and the data, saves the nonvolatile registers and bitslices the round keys as
`vg_aes_ctr32`'s does (`Ctr32.lean`, `Keys.lean`); the groups (`Ecb.lean`) do
the rest; the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.PPC64LE in
/-- PPC64LE contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and `data` may not wrap around the end of
the address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n`
are public; the key schedule and the data are secret. -/
def blocksPPC64LE (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let data : Region := ⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 2048⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .r5).toNat + 16 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat).map
        (f (s.gpr .r4).toNat (Spec.Aes.bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Aes.PPC64LE VG.Proof.Aes

theorem blocksSetup_wp {s : State} {P : State → Prop}
    (h : ∀ s', s'.gpr .r8 = s.gpr .r7 → s'.gpr .r7 = s.gpr .r6 → s'.gpr .r6 = s.gpr .r5 →
      (∀ r, r ≠ .r8 → r ≠ .r7 → r ≠ .r6 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → P s') :
    WP isa (.block blocksSetup) s P := by
  unfold blocksSetup movR
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_nil ?_
  refine h s₃ ?_ ?_ (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
    (fun r h1 h2 h3 => ?_) (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

theorem correct_blocks {crypt4 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt4 f) {s₀ : State}
    (hp : (Proof.Aes.blocksPPC64LE f).pre s₀) :
    WP isa (blocks crypt4) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (Proof.Aes.blocksPPC64LE f).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, hwrap, hR⟩ := hp
  have hwD : (⟨s₀.gpr .r5, 16 * (s₀.gpr .r6).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .r7, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .r3, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  let n := (s₀.gpr .r6).toNat
  have n16 : 16 * n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .r7) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .r7 - s₀.gpr .r5).isLt
    omega_arith
  have hR14 : (s₀.gpr .r4).toNat ≤ 14 := by omega_arith
  let b := s₀.gpr .r7
  let D := s₀.gpr .r5
  let R := (s₀.gpr .r4).toNat
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine blocksSetup_wp fun s₁ r8₁ r7₁ r6₁ o₁ m₁ rd₁ wr₁ => ?_
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (wr₁ ▸ hwS) r8₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  refine keySetup_wp (s := s₂) (R := R) (by rw [g₂, o₁ _ (by decide) (by decide) (by decide)]; simp [R])
    hR14 fun s₃ r3₃ r5₃ r4₃ o₃ m₃ rd₃ wr₃ => ?_
  have g₃ : ∀ r, r ≠ t0 → r ≠ .r3 → r ≠ .r5 → r ≠ .r4 → s₃.gpr r = s₂.gpr r := o₃
  have hb₃ : s₃.gpr sb = b := by
    rw [g₃ sb (by decide) (by decide) (by decide) (by decide), g₂]; exact r8₁
  have f₀₃ : Frame [⟨b, 2048⟩] s₀.mem s₃.mem := by
    rw [m₃, ← m₁]
    exact f₂.sub fun r hr => ⟨⟨b, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .r3) (16 * (R + 1))
  have hk : KSetup s₃ b (s₀.gpr .r3) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .r3, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dSS }
  have hi₃ : KInv s₃ b (s₀.gpr .r3) R w R s₃ :=
    { hj := Nat.le_refl _
      r4 := r4₃
      r3 := by rw [r3₃, g₂, o₁ .r3 (by decide) (by decide) (by decide)]
      r5 := by rw [r5₃, g₂, show sb = .r8 from rfl, r8₁]; simp [keyAddr, b]
      rd := rfl
      wr := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  unfold keyDone
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
  have g₅ : ∀ r ∈ [Reg.r2, .r6, .r7, .r8], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [u₅.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have r7₅ : s₅.gpr .r7 = s₀.gpr .r6 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide), g₂]; exact r7₁
  have r6₅ : s₅.gpr .r6 = D := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide), g₂]; exact r6₁
  have r2₅ : s₅.gpr .r2 = s₀.gpr .r2 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide), g₂,
      o₁ _ (by decide) (by decide) (by decide)]
  have hb₅ : s₅.gpr sb = b := by rw [show sb = .r8 from rfl, g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .r3 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [u₅.gpr, d₄.r5]; exact BitVec.sub_add_cancel _ _
  have fK : Frame (kRegions b) s₃.mem s₅.mem := u₅.mem ▸ d₄.frame
  have hs : ESetup s₅ b D n R w :=
    { scr := by rw [u₅.wr, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [u₅.wr, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [u₅.mem, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega_arith] }
  have data₅ : EcbInv s₀.mem s₅.mem D n 0 (ecbOut f s₀.mem D R w) := by
    refine ecbInv_frame fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dDS.sub_right (scr_sub _ (by omega_arith))) n16
      (ecbInv_frame f₀₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
        n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₅ b D n R w) ?_ fun s₆ gd => ?_)
  · refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_arith)
      (by rw [r7₅]; simp [n])) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega_arith⟩
    · have hn0 : n ≠ 0 := by simpa using h0
      refine ecbGroups_ok hcr hs ⟨by omega_arith, ?_, ?_, hb₅, hK0, rfl, rfl, rfl, Frame.refl _ _, data₅⟩
      · rw [r6₅]; simp
      · rw [r7₅]; simp [n]
  -- The epilogue.
  have sv : Saved s₀ b s₆.mem := by
    have sv₁ : Saved s₀ b s₂.mem := fun i hi => by
      obtain ⟨n6, n7, n8⟩ := sreg_ne_args i hi
      rw [sv₂ i hi, o₁ _ n8 n7 n6]
    refine saved_frame (saved_frame (m₃ ▸ sv₁) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · intro r hr
      simp only [eRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (scr_disj _ (by omega_arith) (by omega_arith)).symm
      · exact (dDS.sub_right (scr_sub _ (by omega_arith))).symm
  obtain ⟨s₇, h₇, rg₇, o₇, -, -, fR⟩ :=
    restore_ok (by rw [gd.wr, u₅.wr, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base sv
  refine WP.of_runBlock ⟨s₇, h₇, ?_⟩
  have dR : ∀ r ∈ [(⟨b, 8 * 58⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dDS.sub_right (Region.sub_prefix (by omega_arith))
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases preserved_saved r hr with rfl | ⟨i, hi, rfl⟩
    · rw [o₇ _ (fun i hi => (sreg_ne_r2 i hi).symm), gd.r2, r2₅]
    · exact rg₇ i hi
  · show Spec.Aes.statesAt s₇.mem D n = _
    rw [statesAt_of_ecbInv (ecbInv_frame fR dR n16 gd.data)]
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl

/-! ## The two functions -/

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct_blocks encrypt4_cryptOk hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide) (by lit_decide)⟩, h₂⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct_blocks decrypt4_cryptOk hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide) (by lit_decide)⟩, h₂⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).pre
    (Proof.Aes.blocksPPC64LE Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).pre
    (Proof.Aes.blocksPPC64LE Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified PPC64LE.target encryptBlocks (Spec.Aes.encryptBlocksContract PPC64LE.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified PPC64LE.target decryptBlocks (Spec.Aes.decryptBlocksContract PPC64LE.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [blocksSat] using blocksSat)

end VG.Proof.Aes.PPC64LE
