module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndBase
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndCount
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86: drawing `PS`

The scan's registers (`head_vp`), and the scan (`scan_vp`): after `j`
octets of the tape (`It P j`), `esi` and `ecx` are the tape's next octet and
how many are left, `edi` and `edx` the end of `PS` so far and how much of it
is left, and the nonzero octets of the first `j` are `PS`'s first (`Kept`).
How many those are is a function of the trace (`cnt`), so every register
the scan branches on or addresses with is the same in two runs; it branches
on whether each octet is zero, which is the trace's, and stops after the
trace's octets (`D`). What the function writes and returns (`Res`), and the
tape's words as its four halves are stored (`words4`, `wp_stTape`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.Impl.RsaPkcs1Enc.X86.Random VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : RP}

/-! ## The scan by the trace -/

theorem nz_succ_le (R : List Byte) (j : Nat) : (nz (R.take (j + 1))).length ≤ (nz (R.take j)).length + 1 := by
  rw [List.take_add_one, nz_append, List.length_append]
  have := nz_length_le (R[j]?.toList)
  have : (R[j]?.toList).length ≤ 1 := by cases R[j]? <;> simp
  omega

namespace In

variable {σ : State} (h : In P σ)
include h

theorem scanN : scanLen P.pl (rB P σ) = P.mask.length := by rw [← h.mask, trace_length]

theorem len_N : P.mask.length ≤ P.len := by
  rw [← h.scanN]; have := scanLen_le P.pl (rB P σ); rwa [Proof.RsaPkcs1Sig.bytesAt_len] at this

theorem cntE {j : Nat} (hj : j ≤ P.mask.length) : (nz ((rB P σ).take j)).length = cnt P.mask j := by
  rw [← h.mask]; exact nz_cnt (by rw [h.scanN]; exact hj)

theorem zeroE {j : Nat} (hj : j < P.mask.length) : (rB P σ).getD j 0 = 0 ↔ P.mask.getD j 0 = 1 := by
  rw [← h.mask]; exact zero_mask (by rw [h.scanN]; exact hj)

theorem cnt_lt {j : Nat} (hj : j < P.mask.length) : cnt P.mask j < P.pl := by
  rw [← h.cntE (Nat.le_of_lt hj)]; exact nz_lt (by rw [h.scanN]; exact hj)

theorem cnt_le {j : Nat} (hj : j ≤ P.mask.length) : cnt P.mask j ≤ P.pl := by
  rcases j with _ | j
  · simp [cnt]
  · have := h.cnt_lt (j := j) (by omega)
    rw [← h.cntE hj]
    rw [← h.cntE (Nat.le_of_lt (by omega : j < P.mask.length))] at this
    have := nz_succ_le (rB P σ) j
    omega

theorem stopE {j : Nat} (hj : j < P.mask.length) :
    j + 1 = P.mask.length ↔ (cnt P.mask (j + 1) = P.pl ∨ j + 1 = P.len) := by
  have := scan_stop_iff (n := P.pl) (R := rB P σ) (j := j) (by rw [h.scanN]; exact hj)
  rw [h.scanN, h.cntE (by omega), Proof.RsaPkcs1Sig.bytesAt_len] at this
  exact this

theorem len_pos (hl : P.len ≠ 0) : 0 < P.mask.length := by
  rw [← h.scanN]
  have hp := h.pl8
  obtain ⟨b, R, e⟩ : ∃ b R, rB P σ = b :: R := by
    cases e : rB P σ with
    | nil => have := congrArg List.length e; rw [Proof.RsaPkcs1Sig.bytesAt_len] at this; simp at this; omega
    | cons b R => exact ⟨b, R, rfl⟩
  rw [e]
  obtain ⟨m, hm⟩ : ∃ m, P.pl = m + 1 := ⟨P.pl - 1, by omega⟩
  rw [hm, scanLen]
  split <;> omega

theorem len1149 : P.len ≤ 1149 := by
  have := h.lenC; have := h.pl1021; simp only [Spec.RsaPkcs1Enc.padEntropy] at *; omega

theorem len_zero (hl : P.len = 0) : P.mask.length = 0 := by
  have := h.len_N; omega

end In

/-! ## `PS` so far -/

/-- The nonzero octets among the first `j` of the tape, at `PS`'s start. -/
def Kept (P : RP) (σ s : State) (j : Nat) : Prop :=
  ∀ i < cnt P.mask j, s.mem (P.lay.fr (oBuf + i)) = (nz ((rB P σ).take j)).getD i 0

/-- After `j` octets of the tape. -/
structure It (P : RP) (j : Nat) (σ s : State) : Prop where
  hs : S P σ s
  jN : j ≤ P.mask.length
  si : s.gpr .esi = P.rnd + BitVec.ofNat 32 j
  cx : s.gpr .ecx = BitVec.ofNat 32 (P.len - j)
  di : s.gpr .edi = P.B + BitVec.ofNat 32 (oBuf + cnt P.mask j)
  dx : s.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask j)
  kept : Kept P σ s j

/-- After `head`: whether the tape is empty. -/
def H0 (P : RP) (σ s : State) : Prop := It P 0 σ s ∧ s.zf = some (decide (P.len = 0))

/-- The scan done. -/
abbrev D (P : RP) (σ s : State) : Prop := It P P.mask.length σ s

theorem sub0 (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x

theorem sp_agree {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp], s₁.gpr r = s₂.gpr r := fun _ _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).2.sp, (hF _ _ h₂).2.sp]

theorem In.fit {σ : State} (h : In P σ) : P.B.toNat + frameBytes + 80 ≤ 2 ^ 32 := by
  have := h.ok.fit
  simp only [Lay.A, RP.argv, List.length_cons, List.length_nil] at this
  simp only [frameBytes] at this ⊢
  omega

theorem In.psLen {σ : State} (h : In P σ) :
    BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ml - 3 = BitVec.ofNat 32 P.pl := by
  have := h.mlK
  rw [Offset.ofNat_sub_ofNat (by omega), show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
    Offset.ofNat_sub_ofNat (by omega)]

/-- `psLen` into `r`. -/
theorem wp_psLen {σ s : State} (hs : S P σ s) {r t : Reg} (hr : r ≠ .esp) (ht : t ≠ .esp) (hrt : r ≠ t)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, S P σ u → u.gpr r = BitVec.ofNat 32 P.pl → (∀ x, x ≠ r → x ≠ t → u.gpr x = s.gpr x) →
      u.mem = s.mem → WP isa (.block is) u Q) :
    WP isa (.block (psLenTo r t ++ is)) s Q := by
  simp only [psLenTo, List.cons_append, List.nil_append]
  refine hs.2.wp_arg (j := 4) (r := r) (by simp) hr fun t1 s1 u1 => ?_
  refine s1.wp_arg (j := 8) (r := t) (by simp) ht fun t2 s2 u2 => ?_
  refine wp_sub fun t3 u3 _ => wp_subi fun t4 u4 _ _ => ?_
  refine k t4 ⟨hs.1, (s2.upd u3 hr).upd u4 hr⟩ ?_ (fun x hx hxt => ?_) (by rw [u4.mem, u3.mem, u2.mem, u1.mem])
  · rw [u4.gpr, u3.gpr, u2.gpr, u2.other _ hrt, u1.gpr]
    exact hs.1.psLen
  · rw [u4.other _ hx, u3.other _ hx, u2.other _ hxt, u1.other _ hx]

theorem head_wp {σ s : State} (hs : S P σ s) : WP isa (.block head) s (H0 P σ) := by
  have hpl := hs.1.pl1021
  have hl := hs.1.len1149
  simp only [head]
  refine wp_psLen hs (r := .edx) (t := .eax) (by decide) (by decide) (by decide) fun t1 s1 d1 o1 m1 => ?_
  refine s1.2.wp_arg (j := 9) (r := .esi) (by simp) (by decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 10) (r := .ecx) (by simp) (by decide) fun t3 s3 u3 => ?_
  refine wp_mov fun t4 u4 => wp_addi fun t5 u5 => wp_cmpi fun t6 u6 _ z6 => WP.block_nil ?_
  have st := ((s3.upd u4 (by decide)).upd u5 (by decide)).fupd u6
  have cx5 : t5.gpr .ecx = BitVec.ofNat 32 P.len := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]; rfl
  refine ⟨⟨⟨hs.1, st⟩, Nat.zero_le _, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; simp
  · rw [u6.gpr, cx5]; rfl
  · rw [u6.gpr, u5.gpr, u4.gpr, u3.other _ (by decide), u2.other _ (by decide), s1.2.sp]; simp [cnt]
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), d1]; simp [cnt]
  · simp [cnt] at hi
  · rw [z6, cx5, sub0, ofNat_beq_zero (by omega_arith)]

theorem head_vp : VP (S P) (.block head) (H0 P) :=
  VP.taint [.esp] head_taint (sp_agree fun _ _ h => h) fun _ _ h => head_wp h

/-! ## One octet -/

/-- After loading octet `j`. -/
structure L1 (P : RP) (j : Nat) (σ s : State) : Prop where
  hs : S P σ s
  jN : j < P.mask.length
  si : s.gpr .esi = P.rnd + BitVec.ofNat 32 (j + 1)
  cx : s.gpr .ecx = BitVec.ofNat 32 (P.len - (j + 1))
  di : s.gpr .edi = P.B + BitVec.ofNat 32 (oBuf + cnt P.mask j)
  dx : s.gpr .edx = BitVec.ofNat 32 (P.pl - cnt P.mask j)
  kept : Kept P σ s j
  ax : s.gpr .eax = ((rB P σ).getD j 0).setWidth 32
  zf : s.zf = some (decide (P.mask.getD j 0 = 1))

theorem In.rnd_fit {σ : State} (h : In P σ) : P.rnd.toNat + P.len ≤ 2 ^ 32 := by
  have := h.ok.fits P.RAND (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.rnd.isLt; omega)] at this

/-- Octet `j` of the tape, in a state of the body. -/
theorem S.byte {σ s : State} (hs : S P σ s) {j : Nat} (hj : j < P.len) :
    s.mem (P.rnd.setWidth 64 + BitVec.ofNat 64 j) = (rB P σ).getD j 0 := by
  have := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.RAND) (by simp))
  simp only at this
  rw [Proof.RsaPkcs1Sig.bytesAt_getD hj, Proof.RsaPkcs1Sig.bytesAt_getD hj] at this
  rw [this, Proof.RsaPkcs1Sig.bytesAt_getD hj]

theorem byte_test (b : Byte) : ((b.setWidth 32 &&& b.setWidth 32) == 0) = decide (b = 0) := by
  rw [BitVec.and_self]
  by_cases hb : b = 0
  · subst hb; rfl
  · have : b.setWidth 32 ≠ 0 := fun e => hb (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth] at this
      exact BitVec.eq_of_toNat_eq (by rw [Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this; simpa using this))
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false hb]

theorem load_wp {σ s : State} {j : Nat} (h : It P j σ s) (hj : j < P.mask.length) :
    WP isa (.block load) s (L1 P j σ) := by
  have hs := h.hs
  have hN := hs.1.len_N
  have hf := hs.1.rnd_fit
  simp only [load]
  refine wp_movzx8 (a := P.rnd.setWidth 64 + BitVec.ofNat 64 j)
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, h.si, addr, BitVec.add_zero]; exact addr_eq (by omega_arith))
    ⟨P.RAND, hs.2.inRo (by simp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun t1 u1 => ?_
  refine wp_addi fun t2 u2 => wp_subi fun t3 u3 _ _ => wp_test fun t4 u4 z4 => WP.block_nil ?_
  have st := (((hs.2.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)).fupd u4
  have ax3 : t3.gpr .eax = ((rB P σ).getD j 0).setWidth 32 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hs.byte (by omega_arith)]
  have ax : t4.gpr .eax = ((rB P σ).getD j 0).setWidth 32 := by rw [u4.gpr, ax3]
  have mm : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨hs.1, st⟩, hj, ?_, ?_, ?_, ?_, fun i hi => by rw [mm]; exact h.kept i hi, ax, ?_⟩
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h.si, add_one32]
  · rw [u4.gpr, u3.gpr, u2.other _ (by decide), u1.other _ (by decide), h.cx, ofNat_pred (by omega_arith)]
    congr 1
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.di]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.dx]
  · rw [z4, ax3, byte_test]
    exact congrArg some (decide_eq_decide.mpr (hs.1.zeroE hj))

theorem load_vp (j : Nat) : VP (fun σ s => It P j σ s ∧ j < P.mask.length) (.block load) (L1 P j) :=
  VP.taint [.esi, .ecx] load_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.si, h₂.1.si]
      · rw [h₁.1.cx, h₂.1.cx]) fun _ _ h => load_wp h.1 h.2

/-- After octet `j`. -/
abbrev A (P : RP) (j : Nat) (σ s : State) : Prop := It P (j + 1) σ s ∧ j < P.mask.length

theorem take_succ_getD (R : List Byte) {j : Nat} (hj : j < R.length) : R.take (j + 1) = R.take j ++ [R.getD j 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem keep_wp {σ s : State} {j : Nat} (h : L1 P j σ s) (hz : eval .ne s = some true) :
    WP isa (.block keep) s (A P j σ) := by
  have hs := h.hs
  have hN := hs.1.len_N
  have hj := h.jN
  have hpl := hs.1.pl1021
  have hlt := hs.1.cnt_lt hj
  have hb : (rB P σ).getD j 0 ≠ 0 := fun e => by
    have := (hs.1.zeroE hj).mp e
    rw [show eval .ne s = s.zf.map (!·) from rfl, h.zf, this] at hz; simp at hz
  have hRl : j < (rB P σ).length := by rw [Proof.RsaPkcs1Sig.bytesAt_len]; omega_arith
  have hnz : nz ((rB P σ).take (j + 1)) = nz ((rB P σ).take j) ++ [(rB P σ).getD j 0] := by
    rw [take_succ_getD _ hRl, nz_ne hb]
  have hc1 : cnt P.mask (j + 1) = cnt P.mask j + 1 := by
    rw [← hs.1.cntE (by omega_arith), ← hs.1.cntE (by omega_arith), hnz, List.length_append]; rfl
  have hF : oBuf + cnt P.mask j + 1 ≤ P.lay.F := by show _ ≤ frameBytes; simp only [oBuf, frameBytes]; omega_arith
  have hfit := hs.1.fit
  simp only [keep]
  refine wp_store8 (a := P.lay.fr (oBuf + cnt P.mask j))
    (by show s.ea ⟨.edi, 0⟩ = _; rw [ea_at, h.di, addr, BitVec.add_zero]
        exact hs.1.ok.addrB (by simp only [Lay.A, RP.argv, List.length_cons, List.length_nil, oBuf, frameBytes]; omega_arith))
    (hs.2.inFr hF) fun t1 u1 => ?_
  refine wp_addi fun t2 u2 => wp_subi fun t3 u3 _ _ => WP.block_nil ?_
  have st1 : P.lay.St σ t1 := hs.2.frameW hF (by
    rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    u1.rd u1.wr (by rw [u1.gpr])
  have st := (st1.upd u2 (by decide)).upd u3 (by decide)
  refine ⟨⟨⟨hs.1, st⟩, by omega_arith, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, hj⟩
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.si]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.cx]
  · rw [u3.other _ (by decide), u2.gpr, u1.gpr, h.di, hc1, add_one32, Nat.add_assoc]
  · rw [u3.gpr, u2.other _ (by decide), u1.gpr, h.dx, hc1, ofNat_pred (by omega_arith)]
    congr 1
  · rw [u3.mem, u2.mem, u1.mem, WriteBytes.writeW8_apply, hnz]
    rw [hc1] at hi
    by_cases e : i = cnt P.mask j
    · subst e
      simp only [↓reduceIte]
      rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by rw [hs.1.cntE (by omega_arith)]),
        hs.1.cntE (by omega_arith), Nat.sub_self, show Reg8.al.reg = .eax from rfl, h.ax]
      simp only [List.getD_cons_zero]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := ((rB P σ).getD j 0).isLt
      omega
    · have hne := Offset.add_ofNat_ne (P.lay.Q) (by simp only [oBuf]; omega_arith : oBuf + i < 2 ^ 64)
        (by simp only [oBuf]; omega_arith : oBuf + cnt P.mask j < 2 ^ 64) (by omega_arith)
      simp only [hne, ↓reduceIte]
      rw [Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by rw [hs.1.cntE (by omega_arith)]; omega_arith)]
      exact h.kept i (by omega_arith)

theorem skip_A {σ s : State} {j : Nat} (h : L1 P j σ s) (hz : eval .ne s = some false) : A P j σ s := by
  have hs := h.hs
  have hj := h.jN
  have hN := hs.1.len_N
  have hm : P.mask.getD j 0 = 1 := by
    rw [show eval .ne s = s.zf.map (!·) from rfl, h.zf] at hz; simpa using hz
  have hb : (rB P σ).getD j 0 = 0 := (hs.1.zeroE hj).mpr hm
  have hRl : j < (rB P σ).length := by rw [Proof.RsaPkcs1Sig.bytesAt_len]; omega_arith
  have hnz : nz ((rB P σ).take (j + 1)) = nz ((rB P σ).take j) := by
    rw [take_succ_getD _ hRl, hb, nz_zero]
  have hc1 : cnt P.mask (j + 1) = cnt P.mask j := by
    rw [← hs.1.cntE (by omega_arith), ← hs.1.cntE (by omega_arith), hnz]
  refine ⟨⟨hs, by omega_arith, h.si, h.cx, by rw [h.di, hc1], by rw [h.dx, hc1], fun i hi => ?_⟩, hj⟩
  rw [hnz]; exact h.kept i (by rw [hc1] at hi; exact hi)

theorem pick_vp (j : Nat) : VP (L1 P j) (.ite .ne (.block keep) (.block [])) (A P j) :=
  VP.ite (fun _ _ h => ⟨_, by show Option.map (!·) _ = _; rw [h.zf]; rfl⟩)
    (fun _ _ _ _ h₁ h₂ => by show eval .ne _ = eval .ne _; simp only [eval]; rw [h₁.zf, h₂.zf])
    (VP.taint [.edi, .edx] keep_taint (fun _ _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.di, h₂.1.di]
        · rw [h₁.1.dx, h₂.1.dx]) fun _ _ h => keep_wp h.1 h.2)
    (VP.block_nil fun _ _ h => skip_A h.1 h.2)

/-- After octet `j`, and whether the scan stops. -/
abbrev Mo (P : RP) (j : Nat) (σ s : State) : Prop := A P j σ s ∧ s.zf = some (decide (j + 1 = P.mask.length))

/-- After `cmp edx, 0`. -/
abbrev Mc (P : RP) (j : Nat) (σ s : State) : Prop := A P j σ s ∧ s.zf = some (decide (cnt P.mask (j + 1) = P.pl))

theorem more_vp (j : Nat) : VP (A P j) more (Mo P j) := by
  refine VP.seq (G := Mc P j) (VP.taint [.edx] cmpEdx_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.dx, h₂.1.dx]) fun σ s h => ?_) ?_
  · have hle := h.1.hs.1.cnt_le h.1.jN
    have hpl := h.1.hs.1.pl1021
    refine wp_cmpi fun t u _ z => WP.block_nil ⟨⟨⟨⟨h.1.hs.1, h.1.hs.2.fupd u⟩, h.1.jN, by rw [u.gpr]; exact h.1.si,
      by rw [u.gpr]; exact h.1.cx, by rw [u.gpr]; exact h.1.di, by rw [u.gpr]; exact h.1.dx,
      fun i hi => by rw [u.mem]; exact h.1.kept i hi⟩, h.2⟩, ?_⟩
    rw [z, h.1.dx, sub0, ofNat_beq_zero (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · refine VP.ite (fun _ _ h => ⟨_, h.2⟩) (fun _ _ _ _ h₁ h₂ => by
        show eval .e _ = eval .e _; simp only [eval]; rw [h₁.2, h₂.2])
      (VP.block_nil fun σ s ⟨h, he⟩ => ⟨h.1, ?_⟩)
      (VP.taint [.ecx] testEcx_taint (fun _ _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.1.cx, h₂.1.1.1.cx]) fun σ s ⟨h, he⟩ => ?_)
    · have hc : cnt P.mask (j + 1) = P.pl := by
        change s.zf = _ at he; rw [h.2] at he; simpa using he
      rw [h.2, hc]
      exact congrArg some (decide_eq_decide.mpr (by rw [h.1.1.hs.1.stopE h.1.2]; simp [hc]))
    · have hc : cnt P.mask (j + 1) ≠ P.pl := by
        change s.zf = _ at he; rw [h.2] at he; simpa using he
      have hN := h.1.1.hs.1.len_N
      have hl := h.1.1.hs.1.len1149
      have hj := h.1.2
      refine wp_test fun t u z => WP.block_nil ⟨⟨⟨⟨h.1.1.hs.1, h.1.1.hs.2.fupd u⟩, h.1.1.jN,
        by rw [u.gpr]; exact h.1.1.si, by rw [u.gpr]; exact h.1.1.cx, by rw [u.gpr]; exact h.1.1.di,
        by rw [u.gpr]; exact h.1.1.dx, fun i hi => by rw [u.mem]; exact h.1.1.kept i hi⟩, hj⟩, ?_⟩
      rw [z, h.1.1.cx, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
      exact congrArg some (decide_eq_decide.mpr (by rw [h.1.1.hs.1.stopE hj]; omega_arith))

/-! ## The loop -/

theorem vp_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨_, _, h₁, _⟩ _ _ => absurd h₁ (h _ _)⟩

/-- `m` iterations left. -/
def Lp (P : RP) (m : Nat) (σ s : State) : Prop := m ≤ P.mask.length ∧ It P (P.mask.length - m) σ s

theorem step_vp (n : Nat) : VP (Lp P (n + 1)) step fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → D P σ s) ∧ (0 < n → Lp P n σ s) := by
  by_cases hn : n + 1 ≤ P.mask.length
  swap
  · exact vp_false fun σ s h => hn h.1
  refine (((load_vp (P := P) (P.mask.length - (n + 1))).seq ((pick_vp _).seq (more_vp _))).mono
    (fun σ s h => ⟨h.2, by have := h.1; omega⟩) fun σ s h => ?_)
  obtain ⟨⟨hi, hj⟩, hz⟩ := h
  have e : P.mask.length - (n + 1) + 1 = P.mask.length - n := by omega
  rw [e] at hi hz
  refine ⟨?_, fun h0 => ?_, fun _ => ⟨by omega, hi⟩⟩
  · show Option.map (!·) s.zf = _
    rw [hz]
    cases n with
    | zero => simp
    | succ m => simp; omega
  · subst h0; simpa using hi

theorem loop_vp : VP (fun σ s => It P 0 σ s ∧ 0 < P.mask.length) (.loop step .ne) (D P) := by
  refine ((VP.loop (I := Lp P) step_vp (P.mask.length - 1)).mono (fun σ s h => ?_) fun _ _ h => h)
  rw [show P.mask.length - 1 + 1 = P.mask.length by have := h.2; omega]
  exact ⟨Nat.le_refl _, by rw [Nat.sub_self]; exact h.1⟩

theorem scan_vp : VP (H0 P) scan (D P) := by
  refine VP.ite (fun _ _ h => ⟨_, by show Option.map (!·) _ = _; rw [h.2]; rfl⟩)
    (fun _ _ _ _ h₁ h₂ => by show eval .ne _ = eval .ne _; simp only [eval]; rw [h₁.2, h₂.2])
    (loop_vp.mono (fun σ s ⟨h, he⟩ => ⟨h.1, ?_⟩) fun _ _ h => h) (VP.block_nil fun σ s ⟨h, he⟩ => ?_)
  · change Option.map (!·) s.zf = _ at he; rw [h.2] at he
    exact h.1.hs.1.len_pos (by simpa using he)
  · change Option.map (!·) s.zf = _ at he; rw [h.2] at he
    have hl : P.len = 0 := by simpa using he
    rw [D, h.1.hs.1.len_zero hl]; exact h.1

/-! ## After the scan -/

/-- The scan done, and whether `PS` is full. -/
def Dz (P : RP) (σ s : State) : Prop := D P σ s ∧ s.zf = some (decide (cnt P.mask P.mask.length = P.pl))

theorem cmp_vp : VP (D P) (.block [.alu .cmp .edx (.imm 0)]) (Dz P) :=
  VP.taint [.edx] cmpEdx_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.dx, h₂.dx]) fun σ s h => by
    have hle := h.hs.1.cnt_le h.jN
    have hpl := h.hs.1.pl1021
    refine wp_cmpi fun t u _ z => WP.block_nil ⟨⟨⟨h.hs.1, h.hs.2.fupd u⟩, h.jN, by rw [u.gpr]; exact h.si,
      by rw [u.gpr]; exact h.cx, by rw [u.gpr]; exact h.di, by rw [u.gpr]; exact h.dx,
      fun i hi => by rw [u.mem]; exact h.kept i hi⟩, ?_⟩
    rw [z, h.dx, sub0, ofNat_beq_zero (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- `Kept` of memory that changed apart from `PS`. -/
theorem Kept.frame {σ s t : State} {j : Nat} (h : Kept P σ s j) (hc : cnt P.mask j ≤ P.pl) (hp : P.pl ≤ 1021)
    {rs : List Region} (hf : Frame rs s.mem t.mem) (hd : ∀ r ∈ rs, Region.Disjoint P.BUF r) : Kept P σ t j :=
  fun i hi => by
    have := hf.bytes (R := P.BUF) hd (by show P.pl ≤ 2 ^ 64; omega) (i := i) (by show i < P.pl; omega)
    rw [show P.lay.fr (oBuf + i) = P.lay.fr oBuf + BitVec.ofNat 64 i from
      (Offset.add_ofNat_add_ofNat _ _ _).symm, this, Offset.add_ofNat_add_ofNat]
    exact h i hi

/-! ## The tape's words -/

theorem wordsAt_two (m : Mem) (p : Addr) :
    Spec.Rsa.wordsAt m p 2 = [m.readW p 64, m.readW (p + BitVec.ofNat 64 8) 64] := by
  simp [Spec.Rsa.wordsAt, List.range_succ]

theorem readW64_halves {m : Mem} {a : Addr} {lo hi : BitVec 32} (h0 : m.readW a 32 = lo)
    (h1 : m.readW (a + BitVec.ofNat 64 4) 32 = hi) : m.readW a 64 = hi ++ lo := by
  show (m.read a 8).setWidth 64 = _
  rw [BitVec.setWidth_eq]
  refine Mem.read_eq_of_bytes (n := 8) fun i hi8 => ?_
  rcases (by omega : i < 4 ∨ 4 ≤ i) with h | h
  · rw [Mem.readW_byte m a h, h0]
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    simp [show 8 * i + j < 32 by omega]
  · obtain ⟨k, rfl⟩ : ∃ k, i = 4 + k := ⟨i - 4, by omega⟩
    rw [show a + BitVec.ofNat 64 (4 + k) = a + BitVec.ofNat 64 4 + BitVec.ofNat 64 k by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat], Mem.readW_byte m _ (by omega : k < 4), h1]
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    simp [show ¬ 8 * (4 + k) + j < 32 by omega]
    congr 1; omega

/-- The tape's two words after its four halves are stored in order. -/
theorem words4 (m : Mem) (p : Addr) (a b c d : BitVec 32) :
    Spec.Rsa.wordsAt ((((m.writeW p a).writeW (p + BitVec.ofNat 64 4) b).writeW
      (p + BitVec.ofNat 64 8) c).writeW (p + BitVec.ofNat 64 12) d) p 2 = [b ++ a, d ++ c] := by
  have sp : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 → ∀ (mm : Mem) (v : BitVec 32),
      (mm.writeW (p + BitVec.ofNat 64 y) v).readW (p + BitVec.ofNat 64 x) 32 = mm.readW (p + BitVec.ofNat 64 x) 32 :=
    fun h hx hy mm v => Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)
  have sp0 : ∀ {y : Nat}, 4 ≤ y → y + 4 ≤ 16 → ∀ (mm : Mem) (v : BitVec 32),
      (mm.writeW (p + BitVec.ofNat 64 y) v).readW p 32 = mm.readW p 32 := by
    intro y hy hy' mm v
    have := sp (x := 0) (y := y) (by omega) (by omega) hy' mm v
    rwa [BitVec.add_zero] at this
  rw [wordsAt_two]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  · exact readW64_halves
      (by rw [sp0 (y := 12) (by omega) (by omega), sp0 (y := 8) (by omega) (by omega),
        sp0 (y := 4) (by omega) (by omega), Mem.readW_writeW_self32])
      (by rw [sp (x := 4) (y := 12) (by omega) (by omega) (by omega),
        sp (x := 4) (y := 8) (by omega) (by omega) (by omega), Mem.readW_writeW_self32])
  · exact readW64_halves
      (by rw [sp (x := 8) (y := 12) (by omega) (by omega) (by omega), Mem.readW_writeW_self32])
      (by rw [Offset.add_ofNat_add_ofNat, Mem.readW_writeW_self32])
theorem zero_append_ofNat {k : Nat} (h : k < 2 ^ 32) :
    ((0 : BitVec 32) ++ BitVec.ofNat 32 k : BitVec 64) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]
  show (0 : Nat) <<< 32 ||| k = k
  rw [Nat.zero_shiftLeft, Nat.zero_or]

theorem In.tape_fit {σ : State} (h : In P σ) : P.tape.toNat + 16 ≤ 2 ^ 32 := by
  have := h.ok.fits P.TAPE (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.tape.isLt; omega)] at this

/-- A store of a word into the tape. -/
theorem wp_stTape {σ s : State} (hs : S P σ s) {b r : Reg} {o : Nat} (ho : o + 4 ≤ 16)
    (hb : s.gpr b = P.tape) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, S P σ t → t.gpr = s.gpr → t.mem = s.mem.writeW (P.tape.setWidth 64 + BitVec.ofNat 64 o) (s.gpr r) →
      Frame [P.TAPE] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨b, o⟩ r :: is)) s Q := by
  have hf := hs.1.tape_fit
  have ha : addr P.tape o = P.tape.setWidth 64 + BitVec.ofNat 64 o := addr_eq (by omega)
  have hc : (P.TAPE : Region).Contains (P.tape.setWidth 64 + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_stm hb (by rw [ha]; exact ⟨P.TAPE, hs.2.inRw (by simp), hc⟩) fun t u => ?_
  rw [ha] at u
  have fr : Frame [P.TAPE] s.mem t.mem := by
    rw [u.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  exact k t ⟨hs.1, hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.TAPE, by simp, fun _ h => h⟩)
    u.rd u.wr (by rw [u.gpr])⟩ u.gpr u.mem fr

/-- `PS`'s place misses the tape. -/
theorem In.buf_tape {σ : State} (h : In P σ) : Region.Disjoint P.BUF P.TAPE := by
  have := h.pl1021
  exact h.ok.stk_fr (R := P.TAPE) (.inr (by simp)) (by show _ ≤ frameBytes + 16; simp only [oBuf, frameBytes]; omega)

/-! ## The result -/

/-- The padding string drawn. -/
abbrev psv (P : RP) (σ : State) : List Byte := nz ((rB P σ).take P.mask.length)

/-- The message. -/
abbrev msgB (P : RP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.msg.setWidth 64) P.ml

/-- The tape's words. -/
abbrev TapeW (P : RP) (m : Mem) (u v : Nat) : Prop :=
  Spec.Rsa.wordsAt m (P.tape.setWidth 64) 2 = [BitVec.ofNat 64 u, BitVec.ofNat 64 v]

/-- What the function writes and returns. -/
def Res (P : RP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  (∃ req, Spec.Rsa.wordsAt m (P.tape.setWidth 64) 2 =
      [BitVec.ofNat 64 (Spec.RsaPkcs1Enc.padSearch P.pl (rB P σ)).used, BitVec.ofNat 64 req] ∧
    (Spec.RsaPkcs1Enc.padSearch P.pl (rB P σ)).Requests (Spec.RsaPkcs1Enc.padEntropy P.pl) req) ∧
  match (Spec.RsaPkcs1Enc.padSearch P.pl (rB P σ)).outcome with
  | .accepted ps => Spec.Rsa.publicPrecompute P.nB = some P.pw →
      Spec.RsaPkcs1Enc.writtenRandom m (P.out.setWidth 64) P.K r (Spec.RsaPkcs1Enc.encrypt P.nB P.eB (msgB P σ) ps)
  | .entropy .. => r = 0 ∧ Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = List.replicate P.K 0
  | .exhausted => r = 3 ∧ Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = List.replicate P.K 0

/-- The end of the body. -/
def Fin (P : RP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .eax)

theorem In.bufA {σ : State} (h : In P σ) : (P.B + BitVec.ofNat 32 oBuf).setWidth 64 = P.lay.fr oBuf :=
  h.ok.addrB (by simp only [Lay.A, RP.argv, List.length_cons, List.length_nil, oBuf, frameBytes]; omega)

end VG.Proof.RsaPkcs1Enc.X86.Rnd
