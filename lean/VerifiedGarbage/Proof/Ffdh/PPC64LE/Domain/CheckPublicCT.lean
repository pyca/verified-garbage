module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `Ffdh.PPC64LE.Domain.CheckPublicFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.Domain.Save`, which this module and modules that import it used -/

section

/-!
# FFDH's domain operations on PPC64LE: saving and restoring the nonvolatile registers

As `Proof/MillerRabin/PPC64LE/Save.lean`: `save ws` stores `r14`–`r31` in
the working space's header words 14–31 (144 bytes at `S + 112`, `S` in
`ws`), and copies `S` into `r23`; `restore` loads them back through `r23`,
`r23` last.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 112

/-- Their 144 bytes. -/
abbrev savR (S : Addr) : Region := ⟨savW S, 144⟩

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (saveOff i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add]; simp only [saveOff]

theorem saved_inj : ∀ i < 18, ∀ j < 18, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 17, saved i ≠ .r23 := by decide

theorem saved_17 : saved 17 = .r23 := rfl

theorem sav_contains (S : Addr) {i : Nat} (hi : i < 18) : (savR S).Contains (off (savW S) (8 * i)) 8 :=
  Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (S : Addr) {i j : Nat} (hi : i < 18) (hj : j < 18) (h : i ≠ j) :
    Mem.Sep (off (savW S) (8 * i)) 8 (off (savW S) (8 * j)) 8 :=
  Offset.sep _ (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The first `n` registers are saved. -/
structure SI (ws : Reg) (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [savR (s₀.gpr ws)] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr ws)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {ws : Reg} (hws : ws ≠ .r0) (s₀ : State)
    (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr ws)) (8 * i)) 8) {n : Nat}
    (hn : n < 18) {s : State} (h : SI ws s₀ n s) :
    WP isa (.block [.store .d (saved n) ws (saveOff n)]) s (SI ws s₀ (n + 1)) := by
  have hw : s.gpr ws = s₀.gpr ws := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr ws + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d hws (show saveOff n < 2 ^ 15 ∧ (saveOff n) % 4 = 0 by simp only [saveOff]; omega_using [hn])
      hout, Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save ws`. -/
structure Saved (ws : Reg) (s₀ : State) (s : State) : Prop where
  keep : Keep [.r23] s₀ s
  r23 : s.gpr .r23 = s₀.gpr ws
  frame : Frame [savR (s₀.gpr ws)] s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off (savW (s₀.gpr ws)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok {ws : Reg} (hws : ws ≠ .r0) (s₀ : State)
    (hin : ∀ i < 18, InRegions s₀.wr (off (savW (s₀.gpr ws)) (8 * i)) 8) :
    WP isa (.block (save ws)) s₀ (Saved ws s₀) := by
  rw [save]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI ws s₀)
    (fun k s hk h => save_step hws s₀ hin hk h) 18 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr ws = s₀.gpr ws := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi hws
    (show 0 < 2 ^ 15 by decide), BitVec.add_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr⟩, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  r23 : s.gpr .r23 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 17) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .r23 (saveOff n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff n)) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn23 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show saveOff n < 2 ^ 15 ∧ (saveOff n) % 4 = 0 by
      simp only [saveOff]; omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn23)]; exact h.r23
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, at `r23`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r23 = S)
    (hsin : ∀ i < 18, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 18, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 17 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 (saveOff 17)) 8 := by
    rw [h.rd, h.wr, h.r23, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 17 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff 17)) 64 = v 17 := by
    rw [h.mem, saveOff_eq]; exact hsav 17 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) (show saveOff 17 < 2 ^ 15 ∧ saveOff 17 % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r23, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_17, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_17 ▸ hr 17 (by decide))]
    exact h.others r hr

end VG.Proof.Ffdh.PPC64LE.Domain

end

end

/-!
# `vg_ffdh_check_public` on PPC64LE: the function

`vg_ffdh_check_public(domain = r3, domain_len = r4, p_len = r5, y = r6,
y_len = r7, scratch = r8, scratch_len = r9)` (`cpContract`): `checkPublic`
saves the nonvolatile registers in the working space's header, sets up the
registers (`setup_ok`), loads and checks p (`loadP_ok`), checks y
(`checkY_ok`) and restores the registers (`cp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- `domain`, `domain_len` bytes at `r3`. -/
abbrev domR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩

/-- `y`, `y_len` bytes at `r6`. -/
abbrev yR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩

/-- The working space, `scratch_len` words at `r8`. -/
abbrev scrR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩

/-- `vg_ffdh_check_public`, on the registers. -/
def cpContract : Contract isa where
  pre s :=
    s.rd = [domR s, yR s] ∧ s.wr = [scrR s] ∧ (domR s).Disjoint (scrR s) ∧ (yR s).Disjoint (scrR s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64 ∧ Spec.Ffdh.pLenValid (s.gpr .r5).toNat ∧
      Spec.Ffdh.domainLenValid (s.gpr .r5).toNat (s.gpr .r4).toNat ∧ (s.gpr .r7).toNat = (s.gpr .r5).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r9).toNat
  post s t :=
    Spec.Ffdh.domainValid (s.gpr .r5).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) = true →
      ((t.gpr .r3).setWidth 32).toNat =
        if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (s.gpr .r5).toNat
          (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat),
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)⟩ then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat).map (·.toNat)

/-- The registers `setup` and the copy of `y` write. -/
def setupRegs : List Reg := [.r10, .r11, .r21, .r26, .r27, .r28, .r29, .r31]

/-- `setup` and `r26 := y`, the working space at `r23`. -/
theorem setup_ok {s : State} {S D Y : Addr} {k L : Nat} (h3 : s.gpr .r3 = D)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 L) (h5 : s.gpr .r5 = BitVec.ofNat 64 k) (h6 : s.gpr .r6 = Y)
    (h23 : s.gpr .r23 = S) (hk : k ≤ 1024) :
    WP isa (.block (setup ++ ([.addi .r26 .r6 0] : List Instr))) s fun t =>
      (t.gpr .r21 = D ∧ t.gpr .r27 = BitVec.ofNat 64 L ∧ t.gpr .r28 = BitVec.ofNat 64 k ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r31 = S ∧ t.gpr .r26 = Y ∧ t.mem = s.mem) ∧
      Keep setupRegs s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h3, h4, h5, h6, h23, BitVec.add_zero, Pub.ofNat_add7_shr3 k (by omega_using [hk]), Pub.ofNat_shl3, Pub.ofNat_shl1,
    hdrBytes]
  refine ⟨?_, by simp [off, slot, hdrBytes]⟩
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

/-- A byte of a buffer apart from the working space is not in it. -/
theorem sep_of_disjoint {D S : Addr} {L Z : Nat} (h : (⟨D, L⟩ : Region).Disjoint ⟨S, Z⟩) (hL : L ≤ 2 ^ 64) :
    ∀ i < L, ∀ x, ofs S x < Z → off D i ≠ x := by
  intro i hi x hx e
  subst e
  refine h _ (Offset.contains_base _ (show i + 1 ≤ L by omega_using [hi]) (by omega_using [hL, hi])) ?_
  show (off D i - S).toNat + 1 ≤ Z
  exact Nat.succ_le_of_lt hx

/-- A buffer's bytes are readable. -/
theorem rd_of_mem {s : State} {D : Addr} {L : Nat} (h : (⟨D, L⟩ : Region) ∈ s.rd) (hL : L ≤ 2 ^ 64) :
    ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1 :=
  fun i hi => ⟨_, List.mem_append_left _ h, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hL, hi])⟩

/-- Bytes apart from the scratch buffer are kept by a write to its saved words. -/
theorem bytes_frame {m m' : Mem} {D S : Addr} {L Z : Nat} (hf : Frame [savR S] m m')
    (h : (⟨D, L⟩ : Region).Disjoint ⟨S, Z⟩) (hL : L ≤ 2 ^ 64) (hZ : 256 ≤ Z) :
    Spec.Rsa.bytesAt m' D L = Spec.Rsa.bytesAt m D L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr hc => ?_
  rw [List.mem_singleton] at hr
  subst hr
  obtain hi := List.mem_range.mp hi
  exact h (D + BitVec.ofNat 64 i) (Offset.contains_base _ (show i + 1 ≤ L by omega_using [hi]) (by omega_using [hL, hi]))
    ((Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega_using [hZ])) _ hc)

theorem pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r23] : List Reg) ++ setupRegs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (checkYRegs ++ ([.r3] : List Reg)) := by
  decide

theorem ret_ofNat (c : Prop) [Decidable c] :
    ((BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32).toNat = if c then 1 else 0 := by
  split <;> rfl

theorem off_off' (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off]; rw [Offset.add_add]

theorem cp_correct (s : State) (h : cpContract.pre s) :
    ∃ tr t, Exec isa checkPublic s tr t ∧ abiPreserved s t ∧ cpContract.post s t := by
  show WP isa checkPublic s fun t => abiPreserved s t ∧ cpContract.post s t
  obtain ⟨hrd, hwr, dDS, dYS, nwD, nwY, nwS, ⟨hk, hk'⟩, hL, hyl, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [domR, yR, scrR] at hrd hwr dDS dYS
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hyl hsl
  generalize hYd : s.gpr .r6 = Y at hrd dYS nwY
  generalize hSd : s.gpr .r8 = S at hwr dDS dYS nwS
  generalize hZd : (s.gpr .r9).toNat * 8 = Z at hwr dDS dYS nwS
  rw [hyl] at hrd dYS nwY
  obtain hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_using [hL]
  obtain hZ256 : 256 ≤ Z := by omega_using [hsl, hZd]
  generalize hwd : (k + 7) / 8 = w
  obtain hw4 : 4 ≤ w := by omega_using [hk, hwd]
  obtain hw' : w ≤ 128 := by omega_using [hk', hwd]
  obtain hZw : slot w 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hwd, hk', hk]
  obtain hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  obtain hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega_using [hZ256, hi]) (by omega_using [hi])⟩
  obtain sepD := sep_of_disjoint dDS (by omega_using [hLd])
  obtain sepY := sep_of_disjoint dYS (by omega_using [hkd])
  obtain rdD := rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega_using [hLd])
  obtain rdY := rd_of_mem (s := s) (D := Y) (L := k) (by rw [hrd]; simp) (by omega_using [hkd])
  unfold checkPublic
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r8) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  obtain h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  obtain hfr₁ : Frame [savR S] s.mem s₁.mem := hSd ▸ hS.frame
  refine WP.mono (setup_ok (D := D) (Y := Y) (L := L) (k := k) ((k1.gpr .r3 (by decide)).trans hDd)
    (by rw [k1.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64]) (by rw [k1.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k1.gpr .r6 (by decide)).trans hYd) h23₁ hk') fun s₂ ⟨⟨a21, a27, a28, a11, a29, a10, a31, a26, m2⟩, k2⟩ => ?_
  rw [hwd] at a11 a29 a10
  obtain k12 := k1.trans k2
  obtain e2 : Env s₂ S Z w := ⟨hs.congr k12.wr, a10, a29, a11, a31, hw4, hw', hZw⟩
  obtain hbD : ∀ n ≤ L, Spec.Rsa.bytesAt s₂.mem D n = Spec.Rsa.bytesAt s.mem D n := fun n hn => by
    rw [m2]; exact bytes_frame hfr₁ (fun x h1 h2 => dDS x (by simp only [Region.Contains] at h1 ⊢; omega_using [hn, h1]) h2)
      (by omega_using [hLd, hn]) hZ256
  obtain hbY : Spec.Rsa.bytesAt s₂.mem Y k = Spec.Rsa.bytesAt s.mem Y k := by
    rw [m2]; exact bytes_frame hfr₁ dYS (by omega_using [hkd]) hZ256
  obtain g23 : s₂.gpr .r23 = S := (k2.gpr .r23 (by decide)).trans h23₁
  refine WP.seq (WP.mono (loadP_ok e2 a21 a28 hwd.symm hk hk' (fun i hi => by
      rw [k12.rd, k12.wr]; exact rdD i (by omega_using [hLk, hi])) (fun i hi => sepD i (by omega_using [hLk, hi])))
    fun s₃ ⟨⟨p3, c3, b3⟩, k3⟩ => ?_)
  rw [hbD k (by omega_using [hLk])] at p3 c3
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) = p at p3 c3
  obtain e3 : Env s₃ S Z w := e2.keep k3 (by decide)
  obtain k13 := k12.trans k3
  obtain hbY₃ : Spec.Rsa.bytesAt s₃.mem Y k = Spec.Rsa.bytesAt s.mem Y k := by
    rw [b3.bytesAt hZw sepY, hbY]
  obtain hbQ₃ : L = 3 * k → Spec.Rsa.bytesAt s₃.mem (off D (2 * k)) k = Spec.Rsa.bytesAt s.mem (off D (2 * k)) k :=
      fun h3k => by
    obtain sq : ∀ i < k, ∀ x, ofs S x < Z → off (off D (2 * k)) i ≠ x := fun i hi => by
      rw [off_off']; exact sepD _ (by omega_using [h3k, hi])
    rw [b3.bytesAt hZw sq]
    have := hbD (3 * k) (by omega_using [h3k])
    simp only [Spec.Rsa.bytesAt] at this ⊢
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    obtain e := congrArg (fun l => l[2 * k + i]?) this
    simp only [List.getElem?_map, List.getElem?_range (show 2 * k + i < 3 * k by omega_using [hi]), Option.map_some,
      Option.some.injEq] at e
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact e
  -- The branch on p's validity.
  obtain hite : WP isa (.ite (.zero .d .r0) checkY (.block [.li .r3 0])) s₃ fun t =>
      (Spec.Rsa.modulusValid p k = true → t.gpr .r3 = BitVec.ofNat 64 (if (1 < Spec.Rsa.os2ip
          (Spec.Rsa.bytesAt s.mem Y k) ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) < p - 1) ∧
          (L = 3 * k → Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Y k) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) % p = 1) then 1 else 0)) ∧
        Body S w s₃.mem t.mem ∧ Keep (checkYRegs ++ [.r3]) s₃ t := by
    refine WP.ite (s₃.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · have hv := c3.mp (by simpa using hb)
      have hv' := hv
      simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv'
      refine WP.mono (checkY_ok (D := D) (Y := Y) (L := L) e3 ((k3.gpr .r23 (by decide)).trans g23)
        ((k3.gpr .r21 (by decide)).trans a21) ((k3.gpr .r26 (by decide)).trans a26)
        ((k3.gpr .r27 (by decide)).trans a27) ((k3.gpr .r28 (by decide)).trans a28) hwd.symm hk hk' hLk.2
        (by rw [p3]; omega_using [hv']) (by rw [p3]; exact hv'.1.1.1)
        (by rw [p3]; exact top_of_valid hv (by omega_using [hwd]) (by omega_using [hw4]))
        (fun i hi => by rw [k13.rd, k13.wr]; exact rdY i hi) sepY
        (fun _ i hi => by rw [k13.rd, k13.wr, off_off']; exact rdD _ (by omega_arith))
        (fun _ i hi => by rw [off_off']; exact sepD _ (by omega_arith)))
        fun t ⟨⟨t3, bt⟩, kt⟩ => ⟨fun _ => ?_, bt, kt.mono (by decide)⟩
      rw [t3, hbY₃, p3]
      congr 1
      by_cases h3k : L = 3 * k
      · rw [hbQ₃ h3k]
      · simp only [h3k, false_imp_iff, and_true]
    · refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 0 ∧ t.mem = s₃.mem) (by prun)
        (by decide)) fun t ⟨⟨_, tm⟩, kt⟩ => ⟨fun hv => absurd (c3.mpr hv) (by simpa using hb),
          by rw [tm]; exact Outside.refl _ _ _ _, kt.mono (by decide)⟩
  refine WP.seq (WP.mono hite fun t₄ ⟨t3, b4, k4⟩ => ?_)
  obtain k14 := k13.trans k4
  obtain hsav : ∀ i < 18, t₄.mem.readW (off (savW S) (8 * i)) 64 = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) :=
      fun i hi => by
    obtain ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    obtain e0 : slot w 0 = 256 := by rw [slot_eq]; omega_using []
    rw [← hS.saved i hi, hSd, ea]
    show Mont.word t₄.mem S (112 + 8 * i) = Mont.word s₁.mem S (112 + 8 * i)
    rw [Outside.word b4 (by omega_using [hi, e0]) (by omega_using [hi]), Outside.word b3 (by omega_using [hi, e0]) (by omega_using [hi]), m2]
  refine WP.mono (restore_ok t₄ ((k4.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans g23))
    (by rw [k14.wr]; exact hin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, k14.sp], by rw [ulr, k14.lr]⟩, fun hdv => ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, k14.gpr r (pres_not_written r hr hn)]
  · rw [hDd, hLd, hkd] at hdv
    obtain hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp] at hmod
    rw [uot .r3 (by decide), t3 hmod, ret_ofNat, hDd, hLd, hkd, hyl, hYd]
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    rw [Proof.Ffdh.publicValid_eq, Proof.Ffdh.domainOf_p _ _ hLk.1, hp]
    refine and_congr Iff.rfl ?_
    simp only [Spec.Ffdh.domainLenValid] at hL
    rcases hL with rfl | rfl
    · rw [Proof.Ffdh.domainOf_q2 _ _ (by omega_using [hk])]
      simp only [reduceCtorEq, false_imp_iff, imp_true_iff, iff_true]
      intro h; omega
    · rw [Proof.Ffdh.domainOf_q3]
      simp only [Option.some.injEq, forall_eq', true_imp_iff]

end VG.Proof.Ffdh.PPC64LE.Domain

end

end

/-!
# `vg_ffdh_check_public` on PPC64LE: constant time

As `Proof/Bignum/PPC64LE/PreCT.lean`: the taint analysis treats memory as
secret, so the bytes of p and y, and what is computed from them, are secret
to it, though they are public. Two runs are related by `Two` at each step,
both satisfying the same predicate for the same public data `CD` (the
pointers, the lengths and the bytes of the domain and y), which fixes what
the code branches on: p's first byte (in `check2`), whether p is valid,
whether `1 < y < p − 1`, and whether there is q. Each piece between them is
checked by the taint analysis from the registers the predicate fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot bytesAt_length)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.Ffdh (lead lead_lt)

/-- The public data of a run: the domain, y and the working space, `p_len`,
`domain_len`, the working space's size in bytes, and the bytes of the domain
and y. -/
structure CD where
  D : Addr
  Y : Addr
  S : Addr
  k : Nat
  L : Nat
  Z : Nat
  db : List Byte
  yb : List Byte

abbrev CD.w (d : CD) : Nat := (d.k + 7) / 8

/-- p. -/
abbrev CD.p (d : CD) : Nat := Spec.Rsa.os2ip (d.db.take d.k)

/-- y. -/
abbrev CD.y (d : CD) : Nat := Spec.Rsa.os2ip d.yb

def cdOf (s : State) : CD :=
  ⟨s.gpr .r3, s.gpr .r6, s.gpr .r8, (s.gpr .r5).toNat, (s.gpr .r4).toNat, (s.gpr .r9).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat⟩

/-- What holds from `setup` on. -/
structure Base (d : CD) (s : State) : Prop where
  env : Env s d.S d.Z d.w
  r21 : s.gpr .r21 = d.D
  r23 : s.gpr .r23 = d.S
  r27 : s.gpr .r27 = BitVec.ofNat 64 d.L
  r28 : s.gpr .r28 = BitVec.ofNat 64 d.k
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hL : d.L = 2 * d.k ∨ d.L = 3 * d.k
  rdD : ∀ i < d.L, InRegions (s.rd ++ s.wr) (off d.D i) 1
  sepD : ∀ i < d.L, ∀ x, ofs d.S x < d.Z → off d.D i ≠ x
  rdY : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.Y i) 1
  sepY : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.Y i ≠ x
  bD : Spec.Rsa.bytesAt s.mem d.D d.L = d.db
  bY : Spec.Rsa.bytesAt s.mem d.Y d.k = d.yb

/-- The registers `Base` fixes. -/
def baseRegs : List Reg := [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r31]

theorem Base.of {d : CD} {s t : State} (h : Base d s) (hg : ∀ r ∈ baseRegs, t.gpr r = s.gpr r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : Body d.S d.w s.mem t.mem) : Base d t where
  env := ⟨h.env.hs.congr hwr, (hg .r10 (by decide)).trans h.env.h10, (hg .r29 (by decide)).trans h.env.h29,
    (hg .r11 (by decide)).trans h.env.h11, (hg .r31 (by decide)).trans h.env.h31, h.env.hw, h.env.hw', h.env.hZ⟩
  r21 := (hg _ (by decide)).trans h.r21
  r23 := (hg _ (by decide)).trans h.r23
  r27 := (hg _ (by decide)).trans h.r27
  r28 := (hg _ (by decide)).trans h.r28
  k64 := h.k64
  k1024 := h.k1024
  hL := h.hL
  rdD := by rw [hrd, hwr]; exact h.rdD
  sepD := h.sepD
  rdY := by rw [hrd, hwr]; exact h.rdY
  sepY := h.sepY
  bD := by rw [hm.bytesAt h.env.hZ h.sepD]; exact h.bD
  bY := by rw [hm.bytesAt h.env.hZ h.sepY]; exact h.bY

theorem Base.keep {d : CD} {s t : State} {rs : List Reg} (h : Base d s) (k : Keep rs s t)
    (hm : Body d.S d.w s.mem t.mem) (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base d t :=
  h.of (fun r hr' => k.gpr r (hr r hr')) k.rd k.wr hm

theorem Base.same {d : CD} {s t : State} {rs : List Reg} (h : Base d s) (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base d t :=
  h.keep k (by rw [hm]; exact Outside.refl _ _ _ _) hr

theorem Base.pins {d : CD} {s₁ s₂ : State} (h₁ : Base d s₁) (h₂ : Base d s₂) :
    ∀ r ∈ baseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.env.h10, h₂.env.h10]
  · rw [h₁.env.h11, h₂.env.h11]
  · rw [h₁.r21, h₂.r21]
  · rw [h₁.r23, h₂.r23]
  · rw [h₁.r27, h₂.r27]
  · rw [h₁.r28, h₂.r28]
  · rw [h₁.env.h29, h₂.env.h29]
  · rw [h₁.env.h31, h₂.env.h31]

/-- A branch on a register that each predicate fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {r : Reg} {t e : Prog isa} {Q : State → State → Prop}
    (hfix : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (s₁.gpr r = 0 ↔ s₂.gpr r = 0))
    (ht : RelCT isa (Two fun a s => Φ a s ∧ s.gpr r = 0) t Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ s.gpr r ≠ 0) e Q) :
    RelCT isa (Two Φ) (.ite (.zero .d r) t e) Q := by
  refine RelCT.ite (fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => ?_) (RelCT.mono ht (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_)
    fun _ _ h => h) (RelCT.mono he (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
  · rw [eval_zero, eval_zero]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact hfix a s₁ s₂ h₁ h₂
  · rw [eval_zero] at hc
    have h0 : s₁.gpr r = 0 := by simpa using hc
    exact ⟨a, ⟨h₁, h0⟩, ⟨h₂, (hfix a s₁ s₂ h₁ h₂).mp h0⟩, hsp⟩
  · rw [eval_zero] at hc
    have h0 : s₁.gpr r ≠ 0 := by simpa using hc
    exact ⟨a, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 ((hfix a s₁ s₂ h₁ h₂).mpr e)⟩, hsp⟩

theorem byte_of_bytesAt {m : Mem} {P : Addr} {n i : Nat} {l : List Byte} (h : Spec.Rsa.bytesAt m P n = l)
    (hi : i < n) : m (off P i) = l[i]'(by rw [← h, bytesAt_length]; exact hi) := by
  subst h
  simp [Spec.Rsa.bytesAt, off]

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

/-! ## The predicates -/

def C0 (d : CD) (s : State) : Prop := cpContract.pre s ∧ cdOf s = d

/-- After `setup`. -/
def C1 (d : CD) (s : State) : Prop := Base d s ∧ s.gpr .r26 = d.Y

/-- With `loadN`'s arguments. -/
def C1a (d : CD) (s : State) : Prop := C1 d s ∧ s.gpr .r12 = off d.D 0 ∧ s.gpr .r6 = BitVec.ofNat 64 d.k

/-- After `loadN`. -/
def C2 (d : CD) (s : State) : Prop := C1a d s ∧ arr s.mem d.S d.w 0 = d.p

/-- After `check1`. -/
def C3 (d : CD) (s : State) : Prop :=
  C1 d s ∧ arr s.mem d.S d.w 0 = d.p ∧ s.gpr .r6 = BitVec.ofNat 64 d.k ∧
    s.gpr .r15 = BitVec.ofNat 64 ((d.db.take d.k).getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ ((d.db.take d.k).getD (d.k - 1) 0).toNat % 2 = 1)

/-- After `check2`. -/
def C4 (d : CD) (s : State) : Prop :=
  C1 d s ∧ arr s.mem d.S d.w 0 = d.p ∧ (s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid d.p d.k = true)

/-- After `range`. -/
def C5 (d : CD) (s : State) : Prop :=
  Base d s ∧ arr s.mem d.S d.w 0 = d.p ∧ Spec.Rsa.modulusValid d.p d.k = true ∧
    (s.gpr .r26 = 0 ↔ ¬ (1 < d.y ∧ d.y < d.p - 1))

/-- After `hasQ`. -/
def C6 (d : CD) (s : State) : Prop :=
  Base d s ∧ arr s.mem d.S d.w 0 = d.p ∧ Spec.Rsa.modulusValid d.p d.k = true ∧ (s.gpr .r0 = 0 ↔ d.L = 3 * d.k)

/-- Before `restore`. -/
def CF (d : CD) (s : State) : Prop := s.gpr .r23 = d.S

theorem pins_C0 : Pins C0 [.r3, .r4, .r5, .r6, .r8] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (congrArg CD.D h₁).trans (congrArg CD.D h₂).symm
  · exact BitVec.eq_of_toNat_eq ((congrArg CD.L h₁).trans (congrArg CD.L h₂).symm)
  · exact BitVec.eq_of_toNat_eq ((congrArg CD.k h₁).trans (congrArg CD.k h₂).symm)
  · exact (congrArg CD.Y h₁).trans (congrArg CD.Y h₂).symm
  · exact (congrArg CD.S h₁).trans (congrArg CD.S h₂).symm

theorem pins_base {Φ : CD → State → Prop} (h : ∀ d s, Φ d s → Base d s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => (h _ _ h₁).pins (h _ _ h₂)

theorem pins_C1 {Φ : CD → State → Prop} (h : ∀ d s, Φ d s → C1 d s) : Pins Φ (baseRegs ++ ([.r26] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (h _ _ h₁).1.pins (h _ _ h₂).1 r hr
  · rw [List.mem_singleton] at hr; subst hr; rw [(h _ _ h₁).2, (h _ _ h₂).2]

theorem pins_C1a : Pins C1a (baseRegs ++ ([.r26, .r12, .r6] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.2, h₂.1.2]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem pins_C3 : Pins C3 (baseRegs ++ ([.r26, .r6, .r15, .r18] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.1.2, h₂.1.2]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]

theorem pins_CF : Pins CF [.r23] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]

/-! ## The steps, by correctness -/

theorem T01 {d : CD} {s : State} (h : C0 d s) :
    WP isa (.block (save .r8 ++ setup ++ ([.addi .r26 .r6 0] : List Instr))) s (C1 d) := by
  obtain ⟨⟨hrd, hwr, dDS, dYS, nwD, nwY, nwS, ⟨hk, hk'⟩, hL, hyl, hsl⟩, rfl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [domR, yR, scrR] at hrd hwr dDS dYS
  simp only [cdOf]
  rw [hyl]
  rw [hyl] at hrd dYS nwY
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD ⊢
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL ⊢
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hyl hsl hrd dYS nwY ⊢
  generalize hYd : s.gpr .r6 = Y at hrd dYS nwY ⊢
  generalize hSd : s.gpr .r8 = S at hwr dDS dYS nwS ⊢
  generalize hZd : (s.gpr .r9).toNat * 8 = Z at hwr dDS dYS nwS ⊢
  have hZ256 : 256 ≤ Z := by omega_using [hsl, hZd]
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega_using [hZ256, hi]) (by omega_using [hi])⟩
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r8) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have hfr₁ : Frame [savR S] s.mem s₁.mem := hSd ▸ hS.frame
  refine WP.mono (setup_ok (D := D) (Y := Y) (L := L) (k := k) ((k1.gpr .r3 (by decide)).trans hDd)
    (by rw [k1.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k1.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k1.gpr .r6 (by decide)).trans hYd) (hS.r23.trans hSd) hk')
    fun s₂ ⟨⟨a21, a27, a28, a11, a29, a10, a31, a26, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine ⟨⟨⟨hs.congr k12.wr, a10, a29, a11, a31, show 4 ≤ (k + 7) / 8 by omega_using [hk], show (k + 7) / 8 ≤ 128 by omega_using [hk'],
    hZw⟩, a21,
    (k2.gpr .r23 (by decide)).trans (hS.r23.trans hSd), a27, a28, hk, hk',
    by simp only [Spec.Ffdh.domainLenValid] at hL; omega,
    fun i hi => by rw [k12.rd, k12.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega_using [hLd]) i hi,
    sep_of_disjoint (L := L) dDS (by omega_using [hLd]),
    fun i hi => by rw [k12.rd, k12.wr]; exact rd_of_mem (s := s) (D := Y) (L := k) (by rw [hrd]; simp) (by omega_using [hkd]) i hi,
    sep_of_disjoint (L := k) dYS (by omega_using [hkd]), ?_, ?_⟩, a26⟩
  · rw [m2]; exact bytes_frame (L := L) hfr₁ dDS (by omega_using [hLd]) hZ256
  · rw [m2]; exact bytes_frame (L := k) hfr₁ dYS (by omega_using [hkd]) hZ256

theorem TA {d : CD} {s : State} (h : C1 d s) : WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (C1a d) := by
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off d.D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 d.k ∧
    t.mem = s.mem) (by prun [h.1.r21, h.1.r28, BitVec.add_zero]) (by decide)) fun t ⟨⟨a12, a6, m⟩, k⟩ =>
      ⟨⟨h.1.same k m, (k.gpr .r26 (by decide)).trans h.2⟩, a12, a6⟩

theorem TL {d : CD} {s : State} (h : C1a d s) : WP isa Precompute.loadN s (C2 d) := by
  obtain ⟨⟨hb, h26⟩, h12, h6⟩ := h
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hZ := hb.env.hZ
  have hk := hb.k64
  have hk' := hb.k1024
  have hnw := hb.env.hs.nowrap
  have e28 := slot_eq d.w 28
  refine WP.mono (loadN_ok (dA := slot d.w 0) hb.env.hs hb.env.h10 h12 h6 hb.env.h11 (by omega_using [hk]) (by omega_using [hwd])
    (by omega_using [hwd, hk']) (by rw [slot_eq]; omega_using []) (by rw [slot_eq] at hZ ⊢; omega_using [hZ])
    (fun i hi => hb.rdD i (by rcases hb.hL with h | h <;> omega_using [hi, h]))
    (fun i hi => hb.sepD i (by rcases hb.hL with h | h <;> omega_using [hi, h]))) fun t ⟨hv, out, k⟩ => ?_
  have hm : Body d.S d.w s.mem t.mem := Body.of out (Nat.le_refl _) (by rw [slot_eq] at hZ ⊢; omega_using [e28])
  refine ⟨⟨⟨hb.keep k hm, (k.gpr .r26 (by decide)).trans h26⟩, (k.gpr .r12 (by decide)).trans h12,
    (k.gpr .r6 (by decide)).trans h6⟩, ?_⟩
  rw [arr, hv, ← Proof.Ffdh.take_bytesAt _ _ (show d.k ≤ d.L by rcases hb.hL with h | h <;> omega_using [h]), hb.bD]

theorem getD_of_lt' {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem Base.kL {d : CD} {s : State} (h : Base d s) : d.k ≤ d.L := by rcases h.hL with h | h <;> omega_using [h]

theorem Base.take_len {d : CD} {s : State} (h : Base d s) : (d.db.take d.k).length = d.k := by
  have := h.kL
  rw [List.length_take, ← h.bD, bytesAt_length]; omega_using [this]

theorem Base.take_byte {d : CD} {s : State} (h : Base d s) {i : Nat} (hi : i < d.k) :
    s.mem (off d.D i) = (d.db.take d.k)[i]'(by rw [h.take_len]; exact hi) := by
  have := h.kL
  rw [List.getElem_take]
  exact byte_of_bytesAt h.bD (by omega_using [hi, this])

theorem TC1 {d : CD} {s : State} (h : C2 d s) : WP isa (.block Precompute.check1) s (C3 d) := by
  obtain ⟨⟨⟨hb, h26⟩, h12, h6⟩, hp⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := d.D) (nb := d.db.take d.k) h12 h6 hk hl
    (fun i hi => hb.rdD i (by have := hb.kL; omega_using [hi, this])) fun i hi => hb.take_byte hi)
    fun t ⟨⟨i0, i15, i18, im⟩, k⟩ => ⟨⟨hb.same k im, (k.gpr .r26 (by decide)).trans h26⟩, by rw [arr, im]; exact hp,
      (k.gpr .r6 (by decide)).trans h6, by rw [i15, getD_of_lt' (by omega_using [hl, hk])], i18,
      by rw [i0, getD_of_lt' (by omega_using [hl, hk])]⟩

theorem TC2 {d : CD} {s : State} (h : C3 d s) : WP isa Precompute.check2 s (C4 d) := by
  obtain ⟨⟨hb, h26⟩, hp, h6, h15, h18, h0⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check2_ok (nb := d.db.take d.k) h6 hk hb.k1024 hl (by rw [h0, getD_of_lt' (by omega_using [hl, hk])])
    (by rw [h15, getD_of_lt' (by omega_using [hl, hk])]) h18) fun t ⟨a, m, k⟩ =>
    ⟨⟨hb.same k m, (k.gpr .r26 (by decide)).trans h26⟩, by rw [arr, m]; exact hp, a⟩

theorem modulus_facts {p k : Nat} (h : Spec.Rsa.modulusValid p k = true) : 2 ≤ p ∧ p % 2 = 1 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega_using [h]

theorem TR {d : CD} {s : State} (h : C4 d s ∧ s.gpr .r0 = 0) : WP isa range s (C5 d) := by
  obtain ⟨⟨⟨hb, h26⟩, hp, h0⟩, hz⟩ := h
  have hv := h0.mp hz
  have hf := modulus_facts hv
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hk := hb.k64
  refine WP.mono (range_ok hb.env hb.r23 h26 hb.r28 (by omega_using [hk]) (by omega_using [hwd]) hb.rdY hb.sepY (by rw [hp]; omega_using [hf]))
    fun t ⟨⟨_, p4, _, a26, bt, a10⟩, k⟩ => ⟨hb.of (fun r hr => ?_) k.rd k.wr bt, by rw [p4, hp], hv, ?_⟩
  · simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a10, hb.env.h10]
    all_goals exact k.gpr _ (by decide)
  · rw [a26, mask_eq_zero, hp, hb.bY, decide_eq_false_iff_not]

/-- 0 into `r3`. -/
theorem TK0 {Φ : CD → State → Prop} (hΦ : ∀ d s, Φ d s → Base d s) {d : CD} {s : State}
    (h : Φ d s) : WP isa (.block [.li .r3 0]) s (CF d) := by
  refine WP.mono (WP.keep [.r3] (Q := fun _ => True) (by prun; exact ⟨_, rfl⟩) (by decide)) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), (hΦ d s h).r23]

/-- 1 into `r3`. -/
theorem TK1 {Φ : CD → State → Prop} (hΦ : ∀ d s, Φ d s → Base d s) {d : CD} {s : State}
    (h : Φ d s) : WP isa (.block [.li .r3 1]) s (CF d) := by
  refine WP.mono (WP.keep [.r3] (Q := fun _ => True) (by prun; exact ⟨_, rfl⟩) (by decide)) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), (hΦ d s h).r23]

theorem TQ {d : CD} {s : State} (h : C5 d s ∧ s.gpr .r26 ≠ 0) : WP isa (.block hasQ) s (C6 d) := by
  obtain ⟨⟨hb, hp, hv, _⟩, _⟩ := h
  refine WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (d.L = 3 * d.k) ∧ t.mem = s.mem) (by
      unfold hasQ
      prun [hb.r27, hb.r28]
      exact sub_3k_zero (by rcases hb.hL with h | h <;> have := hb.k1024 <;> omega_using [h, this]) (by have := hb.k1024; omega_using [this]))
    (by decide)) fun t ⟨⟨a0, m⟩, k⟩ => ⟨hb.same k m, by rw [arr, m]; exact hp, hv, ?_⟩
  rw [← beq_iff_eq, a0, decide_eq_true_iff]

theorem TS {d : CD} {s : State} (h : C6 d s ∧ s.gpr .r0 = 0) : WP isa subgroup s (CF d) := by
  obtain ⟨⟨hb, hp, hv, h0⟩, hz⟩ := h
  have h3k := h0.mp hz
  have hf := modulus_facts hv
  have hk := hb.k64
  refine WP.mono (subgroup_ok hb.env hb.r23 hb.r21 hb.r28 (by omega_using [hk]) hb.k1024 (by rw [hp]; omega_using [hf])
    (by rw [hp]; exact hf.2) (by rw [hp]; exact top_of_valid hv (by simp only [CD.w]; omega_using []) (by simp only [CD.w]; omega_using [hk]))
    (fun i hi => by rw [off_off']; exact hb.rdD _ (by omega_using [h3k, hi]))
    (fun i hi => by rw [off_off']; exact hb.sepD _ (by omega_using [h3k, hi]))) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), hb.r23]

/-! ## `subgroup`

The scan for q's first nonzero octet branches on q's octets, which the
taint analysis takes as secret: two runs on the same domain take the same
number of iterations (`two_loopD`), the octets being the domain's, and
`subFront` and `subBack` are checked by the taint analysis, the latter from
the pointer and the count the scan leaves. -/

/-- q's octets. -/
abbrev CD.qb (d : CD) : List Byte := (d.db.drop (2 * d.k)).take d.k

/-- What `subgroup` needs. -/
structure SubPre (d : CD) (s : State) : Prop where
  base : Base d s
  hL : d.L = 3 * d.k
  hp : arr s.mem d.S d.w 0 = d.p
  valid : Spec.Rsa.modulusValid d.p d.k = true

/-- The registers the scan and `subBack` start from. -/
def subScanRegs : List Reg := [.r10, .r11, .r23, .r29, .r30, .r31]

/-- Their values before iteration `j` of the scan. -/
def scanVal (d : CD) (j : Nat) : Reg → BitVec 64
  | .r10 => off d.S (slot d.w 0)
  | .r11 => BitVec.ofNat 64 (2 * d.w)
  | .r23 => d.S
  | .r29 => BitVec.ofNat 64 (8 * (d.w + 2))
  | .r30 => off (off d.D (2 * d.k)) j
  | .r31 => BitVec.ofNat 64 (d.k - j)
  | _ => 0

/-- Before iteration `j` of the scan. -/
structure ScanJ (d : CD) (j : Nat) (s : State) : Prop where
  regs : ∀ r ∈ subScanRegs, s.gpr r = scanVal d j r
  le : j ≤ lead d.qb
  len : d.qb.length = d.k
  k1024 : d.k ≤ 1024
  ne : d.qb ≠ []
  rd : ∀ i < d.qb.length, InRegions (s.rd ++ s.wr) (off (off d.D (2 * d.k)) i) 1
  val : ∀ i (h : i < d.qb.length), s.mem (off (off d.D (2 * d.k)) i) = d.qb[i]

theorem ScanJ.pins {d : CD} {j : Nat} {s₁ s₂ : State} (h₁ : ScanJ d j s₁) (h₂ : ScanJ d j s₂) :
    ∀ r ∈ subScanRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.regs r hr).trans (h₂.regs r hr).symm

/-- `subFront`, to the scan's start. -/
theorem SF {d : CD} {s : State} (h : SubPre d s) : WP isa subFront s (ScanJ d 0) := by
  have hb := h.base
  have hf := modulus_facts h.valid
  have hk := hb.k64
  have hk' := hb.k1024
  refine WP.mono (subFront_ok hb.env hb.r23 hb.r21 hb.r28 (by rw [h.hp]; exact hf.2)
    (by rw [h.hp]; exact top_of_valid h.valid (by simp only [CD.w]; omega_using []) (by simp only [CD.w]; omega_using [hk])))
    fun t hm => ?_
  have hL3 := h.hL
  have hql : d.qb.length = d.k := by
    have hdl : d.db.length = 3 * d.k := by rw [← hb.bD, bytesAt_length, hL3]
    simp only [CD.qb, List.length_take, List.length_drop]; omega_using [hdl]
  have hq : Spec.Rsa.bytesAt t.mem (off d.D (2 * d.k)) d.k = d.qb := by
    rw [hm.body.bytesAt hb.env.hZ (fun i hi x hx => by rw [off_off']; exact hb.sepD _ (by omega_using [hL3, hi]) x hx),
      show off d.D (2 * d.k) = d.D + BitVec.ofNat 64 (2 * d.k) from rfl,
      ← VG.Proof.Dsa.bytesAt_slice _ _ (show 2 * d.k + d.k ≤ d.L by omega_using [hL3]), hb.bD]
  refine ⟨fun r hr => ?_, Nat.zero_le _, hql, hk', fun he => by rw [he] at hql; simp at hql; omega_using [hk, hql],
    fun i hi => ?_, fun i hi => ?_⟩
  · simp only [subScanRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm.h10
    · exact hm.h11
    · exact hm.r23
    · exact hm.h29
    · exact hm.r30
    · rw [hm.r31]; rfl
  · rw [hm.keep.rd, hm.keep.wr, off_off']; exact hb.rdD _ (by omega_using [hL3, hql, hi])
  · have e := List.getElem_of_eq hq (i := i) (by rw [bytesAt_length]; omega_using [hql, hi])
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] at e
    exact e

/-- One iteration of the scan. -/
theorem SL (a : CD × Nat) (s : State) (h : ScanJ a.1 a.2 s) :
    WP isa (.block leadBody) s fun s' => isa.eval (.nonzero .d .r17) s' = some (decide (a.2 < lead a.1.qb)) ∧
      (decide (a.2 < lead a.1.qb) = false → ScanJ a.1 (lead a.1.qb) s') ∧
      (decide (a.2 < lead a.1.qb) = true →
        lead a.1.qb + 1 - (a.2 + 1) < lead a.1.qb + 1 - a.2 ∧ ScanJ a.1 (a.2 + 1) s') := by
  rcases a with ⟨d, j⟩
  dsimp only at h
  have h30 := h.regs .r30 (by decide)
  have h31 := h.regs .r31 (by decide)
  refine WP.mono (leadStep_ok (s₀ := s) (by rw [h.len]; exact h.k1024) h.ne h.rd h.val h.le
    ⟨h30, by rw [h31, h.len]; rfl, rfl, Keep.refl _ _⟩) fun t ⟨⟨t30, t31, tm, tk⟩, t17⟩ => ?_
  have hL := lead_lt h.ne
  have hreg : ∀ r ∈ [Reg.r10, .r11, .r23, .r29], t.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact tk.gpr _ (by decide)
  have mk : ∀ j', j' ≤ lead d.qb → t.gpr .r30 = off (off d.D (2 * d.k)) j' →
      t.gpr .r31 = BitVec.ofNat 64 (d.k - j') → ScanJ d j' t := fun j' hj' a30 a31 =>
    ⟨fun r hr => by
      simp only [subScanRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hreg _ (by decide)]; exact h.regs _ (by decide)
      · rw [hreg _ (by decide)]; exact h.regs _ (by decide)
      · rw [hreg _ (by decide)]; exact h.regs _ (by decide)
      · rw [hreg _ (by decide)]; exact h.regs _ (by decide)
      · exact a30
      · exact a31,
     hj', h.len, h.k1024, h.ne, fun i hi => by rw [tk.rd, tk.wr]; exact h.rd i hi,
     fun i hi => by rw [tm]; exact h.val i hi⟩
  refine ⟨?_, fun hg => ?_, fun hg => ?_⟩
  · rw [VG.PPC64LE.eval_nonzero_ofNat' t .r17 (by cases decide (j < lead d.qb) <;> decide) t17]
    cases decide (j < lead d.qb) <;> rfl
  · have hj : j = lead d.qb := by have := h.le; simp at hg; omega_using [this, hg]
    rw [Nat.min_eq_right (by omega_using [hj])] at t30 t31
    exact mk _ (Nat.le_refl _) t30 (by rw [t31, h.len])
  · have hj : j < lead d.qb := by simpa using hg
    rw [Nat.min_eq_left (by omega_using [hj])] at t30 t31
    exact ⟨show lead d.qb + 1 - (j + 1) < lead d.qb + 1 - j by omega_using [hj], mk _ (by omega_using [hj]) t30 (by rw [t31, h.len])⟩

/-- `subgroup` takes the same time in runs on the same public data. -/
theorem subgroup_rel {Φ : CD → State → Prop} (hΦ : ∀ d s, Φ d s → SubPre d s) :
    RelCT isa (Two Φ) subgroup fun _ _ => True := by
  unfold subgroup
  refine RelCT.seq (R := Two fun d s => ScanJ d 0 s)
    (two_post (two_taint _ (pins_base (Φ := Φ) fun d s h => (hΦ d s h).base) (by taint_decide))
      fun d s h => SF (hΦ d s h))
    (RelCT.seq (R := Two fun (a : CD × Nat) s => ScanJ a.1 (lead a.1.qb) s)
      (RelCT.mono (P := Two fun (a : CD × Nat) s => ScanJ a.1 a.2 s)
        (VG.Proof.Ffdh.PPC64LE.ParameterCandidate.two_loopD (fun a => lead a.1.qb + 1 - a.2)
          (fun a => (a.1, a.2 + 1)) (fun a => decide (a.2 < lead a.1.qb))
          (two_taint [.r30, .r31] (fun a s₁ s₂ h₁ h₂ r hr => ScanJ.pins h₁ h₂ r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> decide)) (by taint_decide))
          SL)
        (fun s₁ s₂ ⟨d, h₁, h₂, hsp⟩ => ⟨(d, 0), h₁, h₂, hsp⟩) fun _ _ h => h)
      (two_taintR subScanRegs (fun _ _ _ h₁ h₂ => ScanJ.pins h₁ h₂) (by taint_decide_rel)))

/-! ## Constant time -/

theorem cp_rel : RelCT isa (Two C0) checkPublic fun _ _ => True := by
  unfold checkPublic
  refine RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => T01 h)
    (RelCT.seq (R := Two C4) ?_ (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_C1 fun _ _ h => h) (by taint_decide)) fun _ _ h => TA h)
      (RelCT.seq (two_post (two_taint _ pins_C1a (by taint_decide)) fun _ _ h => TL h)
        (RelCT.seq (two_post (two_taint (Φ := C2) _ (fun d s₁ s₂ h₁ h₂ => pins_C1a d s₁ s₂ h₁.1 h₂.1)
          (by taint_decide)) fun _ _ h => TC1 h)
          (two_post (two_taint _ pins_C3 (by taint_decide)) fun _ _ h => TC2 h)))
  · refine two_ite (fun d s₁ s₂ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_
      (two_post (two_taint _ (pins_base (Φ := fun d s => C4 d s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1.1)
        (by taint_decide)) fun _ _ h => TK0 (Φ := fun d s => C4 d s ∧ s.gpr .r0 ≠ 0) (fun _ _ h => h.1.1.1) h)
    unfold checkY
    refine RelCT.seq (two_post (two_taint _ (pins_C1 (Φ := fun d s => C4 d s ∧ s.gpr .r0 = 0) fun _ _ h => h.1.1)
      (by taint_decide)) fun _ _ h => TR h) (two_ite (Φ := C5) (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
        (two_post (two_taint _ (pins_base (Φ := fun d s => C5 d s ∧ s.gpr .r26 = 0) fun _ _ h => h.1.1)
          (by taint_decide)) fun _ _ h => TK0 (Φ := fun d s => C5 d s ∧ s.gpr .r26 = 0) (fun _ _ h => h.1.1) h)
        (RelCT.seq (two_post (two_taint _ (pins_base (Φ := fun d s => C5 d s ∧ s.gpr .r26 ≠ 0) fun _ _ h => h.1.1)
          (by taint_decide)) fun _ _ h => TQ h)
          (two_ite (Φ := C6) (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
            (two_post (subgroup_rel (Φ := fun d s => C6 d s ∧ s.gpr .r0 = 0) fun _ _ h =>
              ⟨h.1.1, h.1.2.2.2.mp h.2, h.1.2.1, h.1.2.2.1⟩) fun _ _ h => TS h)
            (two_post (two_taint _ (pins_base (Φ := fun d s => C6 d s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1)
              (by taint_decide)) fun _ _ h => TK1 (Φ := fun d s => C6 d s ∧ s.gpr .r0 ≠ 0) (fun _ _ h => h.1.1) h))))

theorem cp_ct : ConstantTime isa cpContract.pre cpContract.pub checkPublic :=
  RelCT.constantTime (cp_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, h6, h7, h8, h9, hb⟩ => ⟨cdOf s, ⟨hs, rfl⟩,
    ⟨ht, by
      have l1 : ((Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat).map (·.toNat)).length =
          ((Spec.Rsa.bytesAt t.mem (t.gpr .r3) (t.gpr .r4).toNat).map (·.toNat)).length := by
        simp only [List.length_map, bytesAt_length, h4]
      obtain ⟨e1, e2⟩ := List.append_inj hb l1
      simp only [cdOf]
      rw [(List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1,
        (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e2]
      simp only [h3, h4, h5, h6, h8, h9]⟩, hsp⟩)
    fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.Domain
