module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Save
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

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
    WP isa (.block (setup ++ [.addi .r26 .r6 0])) s fun t =>
      (t.gpr .r21 = D ∧ t.gpr .r27 = BitVec.ofNat 64 L ∧ t.gpr .r28 = BitVec.ofNat 64 k ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r31 = S ∧ t.gpr .r26 = Y ∧ t.mem = s.mem) ∧
      Keep setupRegs s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h3, h4, h5, h6, h23, BitVec.add_zero, Pub.ofNat_add7_shr3 k (by omega), Pub.ofNat_shl3, Pub.ofNat_shl1,
    hdrBytes]
  refine ⟨?_, by simp [off, slot, hdrBytes]⟩
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

/-- A byte of a buffer apart from the working space is not in it. -/
theorem sep_of_disjoint {D S : Addr} {L Z : Nat} (h : (⟨D, L⟩ : Region).Disjoint ⟨S, Z⟩) (hL : L ≤ 2 ^ 64) :
    ∀ i < L, ∀ x, ofs S x < Z → off D i ≠ x := by
  intro i hi x hx e
  subst e
  refine h _ (Offset.contains_base _ (show i + 1 ≤ L by omega) (by omega)) ?_
  show (off D i - S).toNat + 1 ≤ Z
  exact Nat.succ_le_of_lt hx

/-- A buffer's bytes are readable. -/
theorem rd_of_mem {s : State} {D : Addr} {L : Nat} (h : (⟨D, L⟩ : Region) ∈ s.rd) (hL : L ≤ 2 ^ 64) :
    ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1 :=
  fun i hi => ⟨_, List.mem_append_left _ h, Offset.contains_base _ (by omega) (by omega)⟩

/-- Bytes apart from the scratch buffer are kept by a write to its saved words. -/
theorem bytes_frame {m m' : Mem} {D S : Addr} {L Z : Nat} (hf : Frame [savR S] m m')
    (h : (⟨D, L⟩ : Region).Disjoint ⟨S, Z⟩) (hL : L ≤ 2 ^ 64) (hZ : 256 ≤ Z) :
    Spec.Rsa.bytesAt m' D L = Spec.Rsa.bytesAt m D L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr hc => ?_
  rw [List.mem_singleton] at hr
  subst hr
  have hi := List.mem_range.mp hi
  exact h (D + BitVec.ofNat 64 i) (Offset.contains_base _ (show i + 1 ≤ L by omega) (by omega))
    ((Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega)) _ hc)

theorem pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r23] : List Reg) ++ setupRegs ++ [.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] ++
      (checkYRegs ++ [.r3]) := by
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
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZ256 : 256 ≤ Z := by omega
  generalize hwd : (k + 7) / 8 = w
  have hw4 : 4 ≤ w := by omega
  have hw' : w ≤ 128 := by omega
  have hZw : slot w 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hwd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have sepD := sep_of_disjoint dDS (by omega)
  have sepY := sep_of_disjoint dYS (by omega)
  have rdD := rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega)
  have rdY := rd_of_mem (s := s) (D := Y) (L := k) (by rw [hrd]; simp) (by omega)
  unfold checkPublic
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r8) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  have hfr₁ : Frame [savR S] s.mem s₁.mem := hSd ▸ hS.frame
  refine WP.mono (setup_ok (D := D) (Y := Y) (L := L) (k := k) ((k1.gpr .r3 (by decide)).trans hDd)
    (by rw [k1.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64]) (by rw [k1.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k1.gpr .r6 (by decide)).trans hYd) h23₁ hk') fun s₂ ⟨⟨a21, a27, a28, a11, a29, a10, a31, a26, m2⟩, k2⟩ => ?_
  rw [hwd] at a11 a29 a10
  have k12 := k1.trans k2
  have e2 : Env s₂ S Z w := ⟨hs.congr k12.wr, a10, a29, a11, a31, hw4, hw', hZw⟩
  have hbD : ∀ n ≤ L, Spec.Rsa.bytesAt s₂.mem D n = Spec.Rsa.bytesAt s.mem D n := fun n hn => by
    rw [m2]; exact bytes_frame hfr₁ (fun x h1 h2 => dDS x (by simp only [Region.Contains] at h1 ⊢; omega) h2)
      (by omega) hZ256
  have hbY : Spec.Rsa.bytesAt s₂.mem Y k = Spec.Rsa.bytesAt s.mem Y k := by
    rw [m2]; exact bytes_frame hfr₁ dYS (by omega) hZ256
  have g23 : s₂.gpr .r23 = S := (k2.gpr .r23 (by decide)).trans h23₁
  refine WP.seq (WP.mono (loadP_ok e2 a21 a28 hwd.symm hk hk' (fun i hi => by
      rw [k12.rd, k12.wr]; exact rdD i (by omega)) (fun i hi => sepD i (by omega)))
    fun s₃ ⟨⟨p3, c3, b3⟩, k3⟩ => ?_)
  rw [hbD k (by omega)] at p3 c3
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) = p at p3 c3
  have e3 : Env s₃ S Z w := e2.keep k3 (by decide)
  have k13 := k12.trans k3
  have hbY₃ : Spec.Rsa.bytesAt s₃.mem Y k = Spec.Rsa.bytesAt s.mem Y k := by
    rw [b3.bytesAt hZw sepY, hbY]
  have hbQ₃ : L = 3 * k → Spec.Rsa.bytesAt s₃.mem (off D (2 * k)) k = Spec.Rsa.bytesAt s.mem (off D (2 * k)) k :=
      fun h3k => by
    have sq : ∀ i < k, ∀ x, ofs S x < Z → off (off D (2 * k)) i ≠ x := fun i hi => by
      rw [off_off']; exact sepD _ (by omega)
    rw [b3.bytesAt hZw sq]
    have := hbD (3 * k) (by omega)
    simp only [Spec.Rsa.bytesAt] at this ⊢
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have e := congrArg (fun l => l[2 * k + i]?) this
    simp only [List.getElem?_map, List.getElem?_range (show 2 * k + i < 3 * k by omega), Option.map_some,
      Option.some.injEq] at e
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact e
  -- The branch on p's validity.
  have hite : WP isa (.ite (.zero .d .r0) checkY (.block [.li .r3 0])) s₃ fun t =>
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
        (by rw [p3]; omega) (by rw [p3]; exact hv'.1.1.1)
        (fun i hi => by rw [k13.rd, k13.wr]; exact rdY i hi) sepY
        (fun _ i hi => by rw [k13.rd, k13.wr, off_off']; exact rdD _ (by omega))
        (fun _ i hi => by rw [off_off']; exact sepD _ (by omega)))
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
  have k14 := k13.trans k4
  have hsav : ∀ i < 18, t₄.mem.readW (off (savW S) (8 * i)) 64 = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) :=
      fun i hi => by
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    have e0 : slot w 0 = 256 := by rw [slot_eq]; omega
    rw [← hS.saved i hi, hSd, ea]
    show Mont.word t₄.mem S (112 + 8 * i) = Mont.word s₁.mem S (112 + 8 * i)
    rw [Outside.word b4 (by omega) (by omega), Outside.word b3 (by omega) (by omega), m2]
  refine WP.mono (restore_ok t₄ ((k4.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans g23))
    (by rw [k14.wr]; exact hin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, k14.sp], by rw [ulr, k14.lr]⟩, fun hdv => ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, k14.gpr r (pres_not_written r hr hn)]
  · rw [hDd, hLd, hkd] at hdv
    have hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ hLk.1, hp] at hmod
    rw [uot .r3 (by decide), t3 hmod, ret_ofNat, hDd, hLd, hkd, hyl, hYd]
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    rw [Proof.Ffdh.publicValid_eq, Proof.Ffdh.domainOf_p _ _ hLk.1, hp]
    refine and_congr Iff.rfl ?_
    simp only [Spec.Ffdh.domainLenValid] at hL
    rcases hL with rfl | rfl
    · rw [Proof.Ffdh.domainOf_q2 _ _ (by omega)]
      simp only [reduceCtorEq, false_imp_iff, imp_true_iff, iff_true]
      intro h; omega
    · rw [Proof.Ffdh.domainOf_q3]
      simp only [Option.some.injEq, forall_eq', true_imp_iff]

end VG.Proof.Ffdh.PPC64LE.Domain
