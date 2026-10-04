import VerifiedGarbage.Proof.Aes.X86_64.Ecb

/-!
# AES on whole blocks on x86-64: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt4` and `decrypt4`, and are proven at once, for any transformation of
four blocks with `CryptOk`: the prologue moves the scratch buffer and the
count, saves the callee-saved registers and bitslices the round keys as
`vg_aes_ctr32`'s does (`Ctr32.lean`, `Group.lean`); the groups
(`Ecb.lean`) do the rest; the epilogue restores the registers.
-/

namespace VG.Proof.Aes

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack, and
`data` may not wrap around the end of the address space. `rounds` is 10, 12
or 14. The pointers, `rounds` and `n` are public; the key schedule and the
data are secret. -/
def blocksX86_64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).map
        (f (s.gpr .rsi).toNat (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Aes

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes

theorem blocksSetup_ok (s : State) :
    ∃ s', runBlock isa blocksSetup s = some s' ∧ s'.gpr .r9 = s.gpr .r8 ∧ s'.gpr .r8 = s.gpr .rcx ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by simp only [blocksSetup, movR, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, Option.map_some]; rfl, ?_⟩
  simp only [State.setReg]
  exact ⟨by simp, by simp, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩

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
    (hcr : CryptOk crypt4 f) {s₀ : State}
    (hp : (Proof.Aes.blocksX86_64 f).pre s₀) :
    WP isa (blocks crypt4) s₀ fun s' => gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 f).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, dRD, dRS, hwrap, hR⟩ := hp
  have hwD : (⟨s₀.gpr .rdx, 16 * (s₀.gpr .rcx).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  let n := (s₀.gpr .rcx).toNat
  have n16 : 16 * n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .r8) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .r8 - s₀.gpr .rdx).isLt
    omega
  have hR14 : (s₀.gpr .rsi).toNat ≤ 14 := by omega
  let b := s₀.gpr .r8
  let D := s₀.gpr .rdx
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, r9₁, r8₁, o₁, m₁, rd₁, wr₁⟩ := blocksSetup_ok s₀
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (wr₁ ▸ hwS) r9₁ (by decide)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, r15₃, rdi₃, rsi₃, o₃, m₃, rd₃, wr₃⟩ := keySetup_ok s₂
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have g₃ : ∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₃ r h3 h4 h5, g₂, o₁ r h1 h2]
  have hb₃ : s₃.gpr sb = b := by
    rw [o₃ sb (by decide) (by decide) (by decide), g₂]; exact r9₁
  have f₀₃ : Frame [⟨b, 2048⟩] s₀.mem s₃.mem := by
    rw [m₃, ← m₁]
    exact f₂.sub fun r hr => ⟨⟨b, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  let R := (s₀.gpr .rsi).toNat
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * (R + 1))
  have hk : KSetup s₃ b (s₀.gpr .rdi) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .rdi, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dSS }
  have hi₃ : KInv s₃ b (s₀.gpr .rdi) R w R s₃ :=
    { hj := Nat.le_refl _
      r15 := by rw [r15₃, g₂, o₁ _ (by decide) (by decide)]; simp [R]
      rdi := by rw [rdi₃, g₂, o₁ .rdi (by decide) (by decide), o₁ .rsi (by decide) (by decide)]
      rsi := by rw [rsi₃, g₂, show sb = .r9 from rfl, r9₁]; simp [keyAddr, b]
      rd := rfl
      wr := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  obtain ⟨s₅, h₅, rdi₅, z₅, o₅, m₅, rd₅, wr₅⟩ := keyDone_ok s₄
  refine WP.of_runBlock ⟨s₅, h₅, ?_⟩
  have g₅ : ∀ r ∈ [Reg.rdx, .r8, .r9, .rsp], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [o₅ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have r8₅ : s₅.gpr .r8 = s₀.gpr .rcx := by
    rw [g₅ _ (by simp), o₃ _ (by decide) (by decide) (by decide), g₂]; exact r8₁
  have rdx₅ : s₅.gpr .rdx = D := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hb₅ : s₅.gpr sb = b := by rw [show sb = .r9 from rfl, g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .rdi = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [rdi₅, d₄.rsi]; simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
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
  · have r8₄ : s₄.gpr .r8 = s₀.gpr .rcx := by rw [← o₅ .r8 (by decide)]; exact r8₅
    refine WP.ite (s₀.gpr .rcx == 0) (by simp [X86_64.eval, z₅, r8₄]) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simp only [beq_iff_eq] at h0; simp [n, h0]
      exact WP.block_nil ⟨hb₅, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine ecbGroups_ok hcr hs ⟨by omega, ?_, ?_, hb₅, hK0, rfl, rfl, rfl, Frame.refl _ _, data₅⟩
      · rw [rdx₅]; simp
      · rw [r8₅]; simp [n]
  -- The epilogue.
  have sv : Saved s₀ b s₆.mem := by
    have sv₁ : Saved s₀ b s₂.mem := fun i hi => by
      rw [sv₂ i hi, o₁ _ (by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
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
  obtain ⟨s₇, h₇, rg₇, o₇, fR⟩ :=
    restore_ok (by rw [gd.wr, wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base (by decide) sv
  refine WP.of_runBlock ⟨s₇, h₇, ?_⟩
  have rsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by
    rw [o₇ _ (fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide), gd.rsp, rsp₅]
  have dR : ∀ r ∈ [(⟨b, 8 * 54⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dDS.sub_right (Region.sub_prefix (by omega))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₇ 0 (by omega)
    · exact rg₇ 1 (by omega)
    · exact rsp₇
    · exact rg₇ 2 (by omega)
    · exact rg₇ 3 (by omega)
    · exact rg₇ 4 (by omega)
    · exact rg₇ 5 (by omega)
  · -- The return address is untouched.
    have fG : Frame [⟨b, 2048⟩, ⟨D, 16 * n⟩] s₀.mem s₇.mem := by
      refine ((f₀₃.mono fun r hr => by simp at hr; simp [hr]).trans ((fK.sub fun r hr => ?_).trans
        ((gd.frame.sub fun r hr => ?_).trans (fR.sub fun r hr => ?_))))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨_, by simp, scr_sub _ (by omega)⟩
      · simp only [eRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨b, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨⟨D, 16 * n⟩, by simp, sub_refl _⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨b, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
    refine fG.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · show Spec.Aes.statesAt s₇.mem D n = _
    rw [statesAt_of_ecbInv (ecbInv_frame fR dR n16 gd.data)]
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl

/-! ## The two functions -/

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_blocks encrypt4_cryptOk hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_blocks decrypt4_cryptOk hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified X86_64.target encryptBlocks (Spec.Aes.encryptBlocksContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86_64.target decryptBlocks (Spec.Aes.decryptBlocksContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.Aes.X86_64
