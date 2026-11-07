module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveBody
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Fn.lean`). `deriveKey_correct`:
`vg_dsa_derive_key` meets `dContract`. After `entry` (`dfront_ok`),
`checkParams` either runs `body` (`dbody_ok`) or `zeroOut` (`dzero_ok`), and
`restore` gives back the callee-saved registers (`sfinish_ok`); the result is
the specification's by `deriveKey_spec`, from `Proof/Dsa/Derive.lean`'s
`deriveKeyBytes_eq`. `deriveWith_ok` is this for any check of the domain
(`Prevalidated.setup` for a domain known to pass, `DeriveChecked.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64

/-- The registers `Derive.zeroOut` writes. -/
def dzeroRegs : List Reg := [.t4, .t5, .t2, .s0] ++ zeroLoopRegs ++ [.a0]

/-- `zeroOut`: `out`'s `3 p_len + 2 q_len` octets (`out` from the header's
`Sign.hOut`) := 0, and `a0 := 0`. -/
theorem dzero_ok {s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key x)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 3 * L.pl + 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + (3 * L.pl + 2 * L.ql) ≤ 2 ^ 64) :
    WP isa Derive.zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) = List.replicate (3 * L.pl + 2 * L.ql) 0 ∧
        Outside out 0 (3 * L.pl + 2 * L.ql) s.mem t.mem ∧ t.gpr .a0 = 0) ∧ Keep dzeroRegs s t := by
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  obtain ⟨hin24, hal24⟩ := ScrL.hdr hs hL (d := 24) (by decide) (by decide)
  unfold Derive.zeroOut
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = out ∧ u.mem = s.mem)
    (by brun [Sign.hOut, hr.s6, hin24, hal24]; exact hw) (by decide) (by rfl)) fun u ⟨⟨a4, mu⟩, ku⟩ => ?_
  refine WP.mono (getP_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t5) fun v ⟨⟨b5, mv⟩, kv⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr (ku.trans kv).2.2) hL ((hr.keepM ku mu).keepM kv mv) .t2)
    fun w ⟨⟨b2, mw⟩, kw⟩ => ?_
  refine WP.mono (WP.keep [.t2, .t5, .s0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (3 * L.pl + 2 * L.ql) ∧
      u.gpr .s0 = 0 ∧ u.mem = w.mem)
    (by
      brun [kw.gpr (r := .t5) (by decide), b5, b2, exec_li_zero]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide) (by rfl))
    fun s₁ ⟨⟨a5, a0, m1'⟩, k1'⟩ => ?_
  have k1 := ((ku.trans kv).trans kw).trans k1'
  have m1 : s₁.mem = s.mem := by rw [m1', mw, mv, mu]
  have a4₁ : s₁.gpr .t4 = out := by rw [(kv.trans kw).trans k1' |>.gpr (by decide)]; exact a4
  refine WP.seq (WP.mono (zeroLoop_ok (N := 3 * L.pl + 2 * L.ql) (by omega) (by omega)
      (fun i hi => by rw [k1.2.2]; exact hout i hi) hno a0 a4₁ a5)
    fun t ⟨⟨tz, tout⟩, tk⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = 0 ∧ u.mem = t.mem) (by brun [exec_li_zero])
      (by decide) (by rfl))
    fun u ⟨⟨u0, mu⟩, ku⟩ => ⟨⟨by rw [mu]; exact tz, by rw [mu, ← m1]; exact tout, u0⟩,
      ((k1.trans tk).trans ku).mono (by decide)⟩

/-- The specification's derivation, on the domain's and x's values. -/
theorem deriveKey_spec {m : Mem} {L : Lay} {key x : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.deriveKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)) (Spec.Rsa.bytesAt m x L.ql) =
      if ParamsOk m L key ∧ DeriveOk (pOf m L key) (qOf m L key) (gOf m L key) (kOf m L x) then
        some (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql) ++
          Spec.Dsa.encodeBE L.pl (gOf m L key ^ kOf m L x % pOf m L key) ++ Spec.Rsa.bytesAt m x L.ql)
      else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq hv (VG.Proof.Bignum.bytesAt_length _ _ _)
    (VG.Proof.Bignum.bytesAt_length _ _ _)]
  have ep : (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).take L.pl = Spec.Rsa.bytesAt m key L.pl := by
    have := VG.Proof.Dsa.bytesAt_slice m key (offset := 0) (len := L.pl) (total := 2 * L.pl + L.ql) (by omega)
    simp only [List.drop_zero, BitVec.add_zero] at this
    exact this
  have eq : ((Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).drop L.pl).take L.ql =
      Spec.Rsa.bytesAt m (off key L.pl) L.ql :=
    VG.Proof.Dsa.bytesAt_slice m key (by omega)
  have eg : ((Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).drop (L.pl + L.ql)).take L.pl =
      Spec.Rsa.bytesAt m (off key (L.pl + L.ql)) L.pl :=
    VG.Proof.Dsa.bytesAt_slice m key (by omega)
  simp only [VG.Proof.Dsa.paramsBytes_eq, ep, eq, eg, VG.Proof.Dsa.powMod_eq]
  change (if _ then some (_ ++ Spec.Dsa.encodeBE L.pl (gOf m L key ^ kOf m L x % pOf m L key) ++ _) else none) = _
  split <;> rename_i h₁ <;> split <;> rename_i h₂
  · rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq, and_true] at h₁
    obtain ⟨⟨hs, hp, hq⟩, hgq, hd, ⟨hy, -⟩, hg, hx⟩ := h₁
    exact absurd ⟨⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩, hy, hx⟩ h₂
  · obtain ⟨⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩, hy, hx⟩ := h₂
    have B := VG.Proof.Dsa.supported_bounds hs
    refine absurd ?_ h₁
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
    exact ⟨⟨hs, hp, hq⟩, hgq, hd, ⟨hy, Nat.mod_lt _ (show 0 < pOf m L key by omega)⟩, hg, hx⟩
  · rfl

/-- `vg_dsa_derive_key`'s run, with any check `X` of the domain that runs
`rest` from what `checkParams` leaves exactly when the domain passes
`ParamsOk`, and `fail` otherwise, as `checkParams` does (`checkParams_ok`);
`X` may assume what the caller knows of the domain at entry. -/
theorem deriveWith_ok {X : Prog isa → Prog isa → Prog isa} (s : State) (h : dContract.pre s)
    (hX : ∀ {u : State} {Q : State → Prop} {rest fail : Prog isa},
      Outside (dlayOf s).S 0 (dlayOf s).Z s.mem u.mem → ScrL u (dlayOf s) →
      Regs u (dlayOf s) (s.gpr .a2) (s.gpr .a5) →
      word u.mem (dlayOf s).S hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0 →
      Src u (dlayOf s) (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) →
      (∀ t, ParamsOk u.mem (dlayOf s) (s.gpr .a2) → Checked u t (dlayOf s) (s.gpr .a2) (s.gpr .a5) 0 →
        Kept (dlayOf s) u.mem t.mem → Keep cpRegs u t → WP isa rest t Q) →
      (∀ t, ¬ ParamsOk u.mem (dlayOf s) (s.gpr .a2) → Kept (dlayOf s) u.mem t.mem →
        Regs t (dlayOf s) (s.gpr .a2) (s.gpr .a5) → ScrL t (dlayOf s) → Keep cpRegs u t → WP isa fail t Q) →
      WP isa (X rest fail) u Q) :
    WP isa (.seq (.block Derive.entry) (.seq (X Derive.body Derive.zeroOut) (.block restore))) s fun t =>
      abiPreserved s t ∧ dContract.post s t := by
  suffices main : WP isa (.seq (.block Derive.entry) (.seq (X Derive.body Derive.zeroOut) (.block restore))) s
      fun t => ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ dContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hL := dlayOf_ok h
  have hZ := hL.z256
  have hnwS := hL.nowrap
  have hpre := h
  obtain ⟨hrd, hwr, dOP, dOX, dOS, -, dPS, dXS, -, nwO, nwP, nwX, -, hv, hol, hpl, -, -, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (dlayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩
  have h1 : (s.gpr .a1).toNat = 3 * (dlayOf s).pl + 2 * (dlayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 2 * (dlayOf s).pl + (dlayOf s).ql := hpl
  have srcK := mkSrc (A := s.gpr .a2) (k := 2 * (dlayOf s).pl + (dlayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dPS nwP (s.gpr .a3).isLt (by omega)
  have srcX := mkSrc (A := s.gpr .a5) (k := (dlayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dXS nwX
    (s.gpr .a6).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .a0) (k := 3 * (dlayOf s).pl + 2 * (dlayOf s).ql)
    (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO (s.gpr .a1).isLt (by omega)
  have hno : (s.gpr .a0).toNat + (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) ≤ 2 ^ 64 := by rw [← h1]; exact nwO
  have hout : ∀ t : State, t.wr = s.wr → ∀ i < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql,
      InRegions t.wr (off (s.gpr .a0) i) 1 := fun t ht i hi =>
    ⟨_, by rw [ht, hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hko : ∀ i < 2 * (dlayOf s).pl + (dlayOf s).ql, ∀ y, ofs (s.gpr .a0) y < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql →
      off (s.gpr .a2) i ≠ y := fun i hi y hy =>
    Pub.ne_of_disjoint (Region.Disjoint.symm dOP) (by omega) i (by omega) y (by rw [h1]; exact hy)
  have hxo : ∀ i < (dlayOf s).ql, ∀ y, ofs (s.gpr .a0) y < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql →
      off (s.gpr .a5) i ≠ y := fun i hi y hy =>
    Pub.ne_of_disjoint (Region.Disjoint.symm dOX) (by omega) i (by simp only [dlayOf] at hi ⊢; omega) y
      (by rw [h1]; exact hy)
  -- A change in `out` keeps `scratch`'s header.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .a0) 0 (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) m m' →
      ∀ {d : Nat}, d + 8 ≤ 256 → word m' (dlayOf s).S d = word m (dlayOf s).S d := fun ho d hd =>
    in_word (out_in (o := 0) (N := 3 * (dlayOf s).pl + 2 * (dlayOf s).ql)
      (by simpa only [off, BitVec.add_zero] using ho) (by omega) (by omega) (srcO s rfl rfl).sep)
      (by omega) (by omega)
  have hspec : dRes s = if ParamsOk s.mem (dlayOf s) (s.gpr .a2) ∧ DeriveOk (pOf s.mem (dlayOf s) (s.gpr .a2))
        (qOf s.mem (dlayOf s) (s.gpr .a2)) (gOf s.mem (dlayOf s) (s.gpr .a2)) (kOf s.mem (dlayOf s) (s.gpr .a5))
      then some (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) ++
        Spec.Dsa.encodeBE (dlayOf s).pl (gOf s.mem (dlayOf s) (s.gpr .a2) ^ kOf s.mem (dlayOf s) (s.gpr .a5) %
          pOf s.mem (dlayOf s) (s.gpr .a2)) ++ Spec.Rsa.bytesAt s.mem (s.gpr .a5) (dlayOf s).ql)
      else none := by
    unfold dRes
    rw [h3]
    exact deriveKey_spec hv
  refine WP.seq (WP.mono (dfront_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  have hsav' : ∀ u : State, Kept (dlayOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (s.gpr .a7) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans (F.sav i hi)
  have hwo : ∀ u : State, Kept (dlayOf s) s₁.mem u.mem → word u.mem (dlayOf s).S Sign.hOut = s.gpr .a0 :=
    fun u hu => (hu.word (Or.inr ⟨by simp only [Sign.hOut, hLens]; omega, by simp only [Sign.hOut]; omega⟩)).trans F.outw
  have hwr' : ∀ u : State, ScrL u (dlayOf s) → ∀ i < 13, InRegions u.wr (off (savW (s.gpr .a7)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
  have hal' : ∀ i < 13, (off (savW (s.gpr .a7)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact F.scr.al8 (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega)
  have Out₁ : Outside (dlayOf s).S 0 (dlayOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [dlayOf] at hZ ⊢; omega)
  have hk0 := srcK s rfl rfl
  have ep₁ : pOf s₁.mem (dlayOf s) (s.gpr .a2) = pOf s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [pOf]; rw [(hk0.take (k := (dlayOf s).pl) (by omega)).bytes Out₁ (by omega)]
  have eq₁ : qOf s₁.mem (dlayOf s) (s.gpr .a2) = qOf s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [qOf]; rw [(hk0.sub (o := (dlayOf s).pl) (k := (dlayOf s).ql) (by omega)).bytes Out₁ (by omega)]
  have eg₁ : gOf s₁.mem (dlayOf s) (s.gpr .a2) = gOf s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [gOf]
    rw [(hk0.sub (o := (dlayOf s).pl + (dlayOf s).ql) (k := (dlayOf s).pl) (by omega)).bytes Out₁ (by omega)]
  have ek₁ : kOf s₁.mem (dlayOf s) (s.gpr .a5) = kOf s.mem (dlayOf s) (s.gpr .a5) := by
    simp only [kOf]; rw [(srcX s rfl rfl).bytes Out₁ (by omega)]
  have eb₁ : Spec.Rsa.bytesAt s₁.mem (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) =
      Spec.Rsa.bytesAt s.mem (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) := (srcK s rfl rfl).bytes Out₁ (by omega)
  have ex₁ : Spec.Rsa.bytesAt s₁.mem (s.gpr .a5) (dlayOf s).ql = Spec.Rsa.bytesAt s.mem (s.gpr .a5) (dlayOf s).ql :=
    (srcX s rfl rfl).bytes Out₁ (by omega)
  have hPs : ParamsOk s₁.mem (dlayOf s) (s.gpr .a2) ↔ ParamsOk s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [ParamsOk, ep₁, eq₁, eg₁]
  refine WP.seq (hX Out₁ F.scr F.regs F.lens (srcK s₁ k₁.2.1 k₁.2.2)
    (fun t hP hc Kd kc => ?_) (fun t hn Kd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    refine WP.mono (dbody_ok hL hP hc Kd (hwo t Kd) (srcK t kt.2.1 kt.2.2) (srcX t kt.2.1 kt.2.2)
      (hout t kt.2.2) hno (srcO t kt.2.1 kt.2.2) hko hxo) fun u ⟨⟨ob, r0u, ⟨m, Km, Om⟩, h6u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h6u (hwr' u scru) hal'
      (fun i hi => (outSep Om (by simp only [saveOff]; omega)).trans
        ((Km.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans
          (hsav' t Kd i hi)))) fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    simp only [ep₁, eq₁, eg₁, ek₁, eb₁, ex₁] at ob r0u
    have hres := hspec
    simp only [hPs.mp hP, true_and] at hres
    refine ⟨?_, ?_⟩
    · rw [w0, r0u, ret_ofNat, hres, signStatus_ite]
    · rw [wm, h1, ob, hres]
      split <;> rfl
  · have kt := k₁.trans kc
    refine WP.mono (dzero_ok hL scrt hrt (hwo t Kd) (hout t kt.2.2) hno) fun u ⟨⟨ub, uo, u0⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok ((ku.gpr (by decide)).trans hrt.s6) (hwr' u (scrt.congr ku.2.2)) hal'
      (fun i hi => (outSep uo (by simp only [saveOff]; omega)).trans (hsav' t Kd i hi)))
      fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    have hres : dRes s = none := by
      rw [hspec]
      exact ite_eq_right_iff.mpr fun hx => absurd (hPs.mpr hx.1) hn
    refine ⟨?_, ?_⟩
    · rw [w0, u0, hres]; rfl
    · rw [wm, h1, ub, hres]; rfl

theorem deriveKey_correct (s : State) (h : dContract.pre s) :
    ∃ tr t, Exec isa Derive.derive s tr t ∧ abiPreserved s t ∧ dContract.post s t :=
  deriveWith_ok (X := checkParams) s h fun _ hs hr hl hk hrest hfail =>
    checkParams_ok (dlayOf_ok h) hs hr hl (by decide) hk hrest hfail

end VG.Proof.Dsa.RISCV64
