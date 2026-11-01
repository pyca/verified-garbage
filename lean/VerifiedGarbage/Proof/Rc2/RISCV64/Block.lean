module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Cipher
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Rc2.RISCV64.BlockIO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cipher
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Rc2.RISCV64.BlockIO
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit

/-! # Verified RC2 block encryption and decryption on RISC-V

The rounds read the schedule (`rounds_runsTo`) at `a2`, between the
block's load and store: the schedule itself if it is aligned, else its copy
in the working space (`copyLoop_ok`), as `placeSchedule_run` proves.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The block contract as the code sees it. -/
def blockC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a1, 8⟩
    let scratch : Region := ⟨s.gpr .a2, 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧
      key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .a1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .a0)) (Spec.Rc2.blockAt s.mem (s.gpr .a1))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem scheduleAt_copy {m m' : Mem} {S D : Addr}
    (h : ∀ i < 128, m' (D + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i)) :
    Spec.Rc2.scheduleAt m' D = Spec.Rc2.scheduleAt m S := by
  apply Vector.ext; intro i hi
  simp only [Spec.Rc2.scheduleAt, Vector.getElem_ofFn]
  rw [h _ (by omega), h _ (by omega)]

/-- The schedule's copy: its bytes in the working space, the rest of memory
as it was. -/
theorem copySchedule_run (s : State) (hrd : s.rd = [⟨s.gpr .a0, 128⟩])
    (hwr : ∀ i < 128, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .a2) 128 (s.gpr .a0) 128) :
    WP isa copySchedule s fun t =>
      (∀ i < 128, t.mem (s.gpr .a2 + BitVec.ofNat 64 i) = s.mem (s.gpr .a0 + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr .a2, 128⟩] s.mem t.mem ∧ Keep [.t3, .t4, .t5, .a7] s t := by
  unfold copySchedule
  apply WP.seq
  refine WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun u => u.gpr .t3 = s.gpr .a0 ∧ u.gpr .t4 = s.gpr .a2 ∧
      u.gpr .t5 = BitVec.ofNat 64 128 ∧ u.mem = s.mem) (by rrun) (by rfl) rfl) fun u ⟨⟨u3, u4, u5, um⟩, uk⟩ => ?_
  refine WP.mono (copyLoop_ok (tmp := .a7) (src := .t3) (dst := .t4) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) u (N := 128) (by decide) (by decide) u5
    (fun i hi => by
      rw [uk.2.1, uk.2.2, u3, hrd]
      exact ⟨⟨s.gpr .a0, 128⟩, List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [uk.2.2, u4]; exact hwr i hi) (by rw [u3, u4]; exact hsep))
    fun t ⟨tc, tf, tk⟩ => ⟨fun i hi => by rw [← u4, tc i hi, u3, um], by rw [← um, ← u4]; exact tf,
      (uk.trans tk).mono (by decide)⟩

/-- The schedule the rounds read, at `a2`: aligned, readable and holding the
schedule, the schedule itself or its copy; memory is changed only in the
working space's first 128 bytes. -/
theorem placeSchedule_run (s : State) (hrd : s.rd = [⟨s.gpr .a0, 128⟩])
    (hwr : ∀ i < 128, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .a2) 128 (s.gpr .a0) 128) (hal : (s.gpr .a2).toNat % 8 = 0)
    (hin : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 o) n) :
    WP isa placeSchedule s fun t =>
      (t.gpr .a2).toNat % 8 = 0 ∧
      (∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (t.gpr .a2 + BitVec.ofNat 64 o) n) ∧
      Spec.Rc2.scheduleAt t.mem (t.gpr .a2) = Spec.Rc2.scheduleAt s.mem (s.gpr .a0) ∧
      Frame [⟨s.gpr .a2, 128⟩] s.mem t.mem ∧ Keep [.t0, .t3, .t4, .t5, .a7, .a2] s t := by
  unfold placeSchedule
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = s.gpr .a0 &&& 7#64 ∧ u.mem = s.mem) (by rrun)
    (by rfl) rfl) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
  have ga0 : u.gpr .a0 = s.gpr .a0 := uk.gpr (by decide)
  have ga2 : u.gpr .a2 = s.gpr .a2 := uk.gpr (by decide)
  refine WP.ite _ (rfl : isa.eval (.zero .t0) u = some (u.gpr .t0 == 0)) (fun hz => ?_) (fun hnz => ?_)
  · have h0 : s.gpr .a0 &&& 7#64 = 0 := by rw [← u0]; simpa using hz
    have hal0 : (s.gpr .a0).toNat % 8 = 0 := by
      have e := congrArg BitVec.toNat h0
      rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e
      exact e
    refine WP.mono (WP.keep [.a2] (Q := fun t => t.gpr .a2 = s.gpr .a0 ∧ t.mem = s.mem) (by rrun [ga0, um])
      (by rfl) rfl) fun t ⟨⟨t2, tm⟩, tk⟩ => ?_
    refine ⟨by rw [t2]; exact hal0, fun o n hn => ?_, by rw [t2, tm], by rw [tm]; exact Frame.refl _ _,
      (uk.trans tk).mono (by decide)⟩
    rw [t2, hrd]
    exact ⟨⟨s.gpr .a0, 128⟩, List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ hn (by omega)⟩
  · refine WP.mono (copySchedule_run u (by rw [uk.2.1, ga0]; exact hrd) (fun i hi => by
        rw [uk.2.2, ga2]; exact hwr i hi) (by rw [ga0, ga2]; exact hsep)) fun t ⟨tc, tf, tk⟩ => ?_
    have t2 : t.gpr .a2 = s.gpr .a2 := by rw [tk.gpr (by decide), ga2]
    refine ⟨by rw [t2]; exact hal, by rw [t2]; exact hin, ?_, by rw [← um, ← ga2]; exact tf,
      (uk.trans tk).mono (by decide)⟩
    rw [t2, ← ga2, ← ga0, ← um]
    exact scheduleAt_copy tc

theorem block_wp (d : Spec.Rc2.Direction) (s : State) (hs : (blockC d).pre s) :
    WP isa (blockCode d) s fun s' => (blockC d).post s s' := by
  obtain ⟨hrd, hwr, hal, hfit1, hfit2, hks, hds⟩ := hs
  have inScratch : ∀ o n, o + n ≤ 256 → InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega)⟩
  have inData : ∀ o n, o + n ≤ 8 → InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega)⟩
  unfold blockCode
  apply WP.seq
  refine WP.mono (placeSchedule_run s hrd (fun i hi => inScratch i 1 (by omega))
    (hks.symm.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (Region.contains_self _ _)) hal (fun o n hn => by
      obtain ⟨r, hr, hc⟩ := inScratch o n (by omega); exact ⟨r, List.mem_append_right _ hr, hc⟩))
    fun t₀ ⟨al₀, rd₀, K₀, f₀, k₀⟩ => ?_
  have p1₀ : t₀.gpr .a1 = s.gpr .a1 := k₀.gpr (by decide)
  have B₀ : Spec.Rc2.blockAt t₀.mem (s.gpr .a1) = Spec.Rc2.blockAt s.mem (s.gpr .a1) :=
    Proof.Rc2.blockAt_frame f₀ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hds.sub_right fun a h => by simp only [Region.Contains] at h ⊢; omega
  apply WP.seq
  refine WP.mono (blockLoad_run t₀ (by
      rw [p1₀, k₀.2.1, k₀.2.2]
      obtain ⟨r, hr, hc⟩ := inData 0 4 (by omega)
      rw [BitVec.add_zero] at hc
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [p1₀, k₀.2.1, k₀.2.2]
        obtain ⟨r, hr, hc⟩ := inData 4 4 (by omega); exact ⟨r, List.mem_append_right _ hr, hc⟩))
    fun t₁ ⟨H₁, m₁, k₁⟩ => ?_
  apply WP.seq
  have E : KeyEnv (t₀.gpr .a2) t₁ := ⟨k₁.gpr (by decide), al₀, fun o n hn => by
    rw [k₁.2.1, k₁.2.2, k₀.2.1, k₀.2.2]; exact rd₀ o n hn⟩
  refine WP.mono (rounds_runsTo d t₁ E rfl _ H₁) fun t₂ ⟨H₂, m₂, k₂⟩ => ?_
  have p4 : t₂.gpr .a1 = s.gpr .a1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide), p1₀]
  refine WP.mono (blockStore_run t₂ H₂
    (by rw [p4, k₂.2.2, k₁.2.2, k₀.2.2]; simpa using inData 0 4 (by omega))
    (by rw [p4, k₂.2.2, k₁.2.2, k₀.2.2]; exact inData 4 4 (by omega)))
    fun t₃ ⟨m₃, _⟩ => ?_
  change Spec.Rc2.blockAt t₃.mem (s.gpr .a1) = _
  rw [m₃, p4, m₂, Proof.Rc2.blockAt_write64, cipher_rounds, m₁, K₀, p1₀, B₀]

/-- The registers the block functions write: no preserved register, nor `ra`. -/
def blockRegs : List Reg := [.a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5]

theorem block_ok (d : Spec.Rc2.Direction) (hw : writesOnly blockRegs (blockCode d) = true)
    (hn : callFree (blockCode d) = true) (s : State) (hs : (blockC d).pre s) :
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep blockRegs (block_wp d s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem block_agree (d : Spec.Rc2.Direction) : ∀ s₁ s₂, (blockC d).pre s₁ → (blockC d).pre s₂ →
    (blockC d).pub s₁ s₂ → taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem encrypt_ct : ConstantTime isa (blockC .encrypt).pre (blockC .encrypt).pub encryptBlock :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (block_agree .encrypt) (by taint_decide)

theorem decrypt_ct : ConstantTime isa (blockC .decrypt).pre (blockC .decrypt).pub decryptBlock :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (block_agree .decrypt) (by taint_decide)

def blockSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_verified : Verified RISCV64.target encryptBlock (Proof.Rc2.encryptBlockContract RISCV64.abi) := by
  refine Verified.of_correct (k := blockC .encrypt) (block_ok .encrypt (by lit_decide) (by lit_decide))
    encrypt_ct ?_
  sig_implies [Proof.Rc2.encryptBlockContract, Proof.Rc2.blockSig, RISCV64.abi, RISCV64.argRegs, blockC, cipher]
    [blockSat] using blockSat

theorem decrypt_verified : Verified RISCV64.target decryptBlock (Proof.Rc2.decryptBlockContract RISCV64.abi) := by
  refine Verified.of_correct (k := blockC .decrypt) (block_ok .decrypt (by lit_decide) (by lit_decide))
    decrypt_ct ?_
  sig_implies [Proof.Rc2.decryptBlockContract, Proof.Rc2.blockSig, RISCV64.abi, RISCV64.argRegs, blockC, cipher]
    [blockSat] using blockSat

end VG.Proof.Rc2.RISCV64
