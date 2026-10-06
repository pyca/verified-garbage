import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMr
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail

/-!
# A candidate on AArch64: constant time of the tail

`montSetup` (`montSetup_ct`, then `montSetup_ok` for what Miller–Rabin
needs), `millerRabin` (`millerRabin_ct`) and the result (`mrResult_ct`),
which branches on `kStat`, which the shape of the test's result fixes, and
stores through `used`'s pointer and `out`, pinned after their loads:
`kTail_ct`, for runs related by `TS`.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

/-! ## The result -/

/-- The status `millerRabin` leaves, from the shape of its result. -/
def statOf (S : Option (Bool × Nat)) : Nat :=
  match S with
  | none => 0
  | some (b, _) => if b then 1 else 3

/-- Before `mrResult`. -/
def EndQ (q : FPub) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) ∧
    word s.mem q.B (8 * kUsedP) = q.up ∧ OutUp s q.B q.Z q.op q.up (8 * q.w) ∧
    word s.mem q.B (8 * kStat) = BitVec.ofNat 64 (statOf q.sch.mr)

theorem loopEnd_endq {q : FPub} {s : State} (h : LoopEnd q s) : EndQ q s := by
  obtain ⟨-, -, c, r, s₀, res, ⟨⟨bm, hc⟩, h0, h1, hf, k⟩, hS, -, hO, hU, hK, ho⟩ := h
  have hw : ∀ {i : Nat}, (i = kRand ∨ i = kLen ∨ i = kRandLen ∨ i = kChecks ∨ i = kOut ∨ i = kUsedP) →
      word s.mem q.B (8 * i) = word s₀.mem q.B (8 * i) := fun hi =>
    hf.word_eq (roundRanges_hdr _ hi) (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨hc.ws, (hw (by simp)).trans hO, (hw (by simp)).trans hK, (hw (by simp)).trans hU, ho.congr k.wr, ?_⟩
  rw [← hS]
  rcases hres : res with _ | ⟨b, rest⟩
  · exact h0 hres
  · exact (h1 b rest hres).1

theorem pins_endq {Φ : FPub → State → Prop} (h : ∀ q s, Φ q s → EndQ q s) : Pins Φ [.x0] :=
  pins_ws' (fun q : FPub => q.B) (fun q : FPub => q.Z) (fun q : FPub => q.w) fun _ _ hx => (h _ _ hx).1

/-- The load of `used`'s pointer after `l`. -/
theorem upLoad_ok {s : State} {q : FPub} (h : EndQ q s) {l : List Instr} (hl : l = [movi .x3 0] ∨ l = [ldh .x3 kUsed]) :
    WP isa (.block (l ++ [ldh .x2 kUsedP])) s fun t => ∀ r ∈ [Reg.x2], t.gpr r = q.up := by
  obtain ⟨hw, -, -, hU, -⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega)
  refine WP.mono (Q := fun (t : State) => t.gpr .x2 = q.up) ?_ fun t h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h
  rcases hl with rfl | rfl
  · brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hl' kUsedP (by decide), hU]
  · brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kUsed < 32 by decide), hl' kUsedP (by decide),
      hl' kUsed (by decide), hU]

/-- `finNone` and `finUsed r`: a load of `used`'s pointer, then the store. -/
theorem finStore_ct {Φ : FPub → State → Prop} (hE : ∀ q s, Φ q s → EndQ q s) {l : List Instr} (r : Nat)
    (hl : l = [movi .x3 0] ∨ l = [ldh .x3 kUsed]) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (l ++ [ldh .x2 kUsedP])) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht' : (taint.check (Taint.ofRegs [.x2]) (.block ([st .x3 .x2, movi .x0 r] : List Instr)) hc').isSome = true) :
    RelCT isa (Two Φ) (.block ((l ++ [ldh .x2 kUsedP]) ++ ([st .x3 .x2, movi .x0 r] : List Instr)))
      fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => ∀ r ∈ [Reg.x2], t.gpr r = q.up) [.x0] (pins_endq hE) ht
    fun _ _ h => upLoad_ok (hE _ _ h) hl) (two_taint [.x2] (pins_of _ (fun q _ => q.up) fun _ _ h => h) ht'))

/-- The registers `storeBE` needs. -/
def soVal' (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => base
  | .x1 => ptr + BitVec.ofNat 64 len
  | _ => BitVec.ofNat 64 len

/-- The block before `storeBE` (as `CvCTMain.lean`'s `storeBlk_ok`). -/
theorem storeBlk_ok' {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem B (8 * sPtr) = ptr)
    (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 Public.sMask]))
      s fun t => ∀ r ∈ [Reg.x0, .x8, .x1, .x9], t.gpr r = soVal' B (off B (slot w j)) ptr len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok j .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x9, .x15] (Q := fun t => t.gpr .x1 = ptr + BitVec.ofNat 64 len ∧
          t.gpr .x9 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc hP, hdr_enc hL, hdr_enc (show Public.sMask < 32 by decide), m₃, m₂, hl₃ sPtr hP,
            hl₃ sLen hL, hl₃ Public.sMask (by decide), hp, hl])
        rfl rfl rfl)
      fun t ⟨⟨h1, h9⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h9))

/-- After `used` is written: the working space and `out`. -/
def EndO (q : FPub) (s : State) : Prop :=
  Ws s q.B q.Z q.w ∧ word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w)

theorem finPrime_eq : finPrime = .seq (.block (([ldh .x3 kUsed] ++ [ldh .x2 kUsedP]) ++ ([st .x3 .x2] : List Instr)))
    (.seq (.block (ws ++ base aN .x8 ++ [ldh .x1 kOut, ldh .x9 kLen, .add .x .x1 .x1 .x9, ldh .x15 Public.sMask]))
      (.seq storeBE (.block [movi .x0 1]))) := rfl

theorem finPrime_ct {Φ : FPub → State → Prop} (hE : ∀ q s, Φ q s → EndQ q s) :
    RelCT isa (Two Φ) finPrime fun _ _ => True := by
  rw [finPrime_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => EndQ q t ∧ t.gpr .x2 = q.up) [.x0]
    (pins_endq hE) (by taint_decide) fun q s h => ?_) (two_piece (Ψ := EndO) [.x2] (pins_of _ (fun q _ => q.up)
      fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide)
      fun q s h => ?_))) (RelCT.seq (two_piece [.x0] (pins_ws' (fun q : FPub => q.B) (fun q : FPub => q.Z)
        (fun q : FPub => q.w) fun _ _ h => h.1) (by taint_decide) fun q s h =>
          storeBlk_ok' h.1 (show kOut < 32 by decide) (show kLen < 32 by decide) h.2.1 h.2.2)
      (two_taint _ (pins_of _ (fun q => soVal' q.B (off q.B (slot q.w aN)) q.op (8 * q.w)) fun _ _ h => h)
        (by taint_decide)))
  · have he := hE q s h
    refine WP.mono (WP.keep [.x3, .x2] (Q := fun t => t.gpr .x2 = q.up ∧ t.mem = s.mem)
      (WP.and (WP.mono (upLoad_ok he (.inr rfl)) fun t h => h .x2 (by simp)) (by
        have hw := he.1
        have hn := hw.scr.nowrap
        have h256 := hw.h256
        brun [hw.x0, hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kUsed < 32 by decide),
          hw.scr.ld (d := 8 * kUsedP) (by simp only [kUsedP, sFn]; omega),
          hw.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega)]))
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h2, hm⟩, k⟩ => ⟨?_, h2⟩
    obtain ⟨hw, hO, hK, hU, ho, hS⟩ := he
    exact ⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
      by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS⟩
  · obtain ⟨⟨hw, hO, hK, hU, ho, -⟩, h2⟩ := h
    have h256 := hw.h256
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW q.up (s.gpr .x3)) (by
      have hup : q.up + BitVec.ofNat 64 0 = q.up := off_zero q.up
      brun [h2, hup, ho.upw]) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    have f : Frm q.B [(q.Z, 2 ^ 64)] s.mem t.mem := by rw [hm]; exact frm_up ho.upZ _ _
    have hw' : ∀ i < 32, word t.mem q.B (8 * i) = word s.mem q.B (8 * i) := fun i hi =>
      f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
    exact ⟨hw.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.past h256 _) k (by decide),
      (hw' _ (by decide)).trans hO, (hw' _ (by decide)).trans hK⟩

theorem statOf_lt (S : Option (Bool × Nat)) : statOf S < 4 := by
  unfold statOf; split <;> (try split) <;> decide

/-- The result leaks the same in runs that agree on the public data. -/
theorem mrResult_ct : RelCT isa (Two EndQ) mrResult fun _ _ => True := by
  unfold mrResult
  refine RelCT.seq (two_piece (Ψ := fun q t => EndQ q t ∧ t.gpr .x3 = BitVec.ofNat 64 (statOf q.sch.mr)) [.x0]
    (pins_endq fun _ _ h => h) (by taint_decide) fun q s h => ?_)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
      (finStore_ct (fun _ _ h => h.1.1) 0 (.inl rfl) (by taint_decide) (by taint_decide))
      (RelCT.seq (two_piece (Ψ := fun q t => EndQ q t ∧
          t.gpr .x3 = BitVec.ofNat 64 (statOf q.sch.mr) - BitVec.ofNat 64 1) [] (pins_nil' _) (by taint_decide)
        fun q s h => ?_)
        (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
          (finPrime_ct fun _ _ h => h.1.1)
          (finStore_ct (fun _ _ h => h.1.1) 3 (.inr rfl) (by taint_decide) (by taint_decide)))))
  · obtain ⟨hw, hO, hK, hU, ho, hS⟩ := h
    have hn := hw.scr.nowrap
    have h256 := hw.h256
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (statOf q.sch.mr) ∧ t.mem = s.mem)
      (by brun [hw.x0, hdr_enc (show kStat < 32 by decide), hw.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega),
        hS]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ =>
      ⟨⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
        by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS⟩, h3⟩
  · obtain ⟨⟨⟨hw, hO, hK, hU, ho, hS⟩, h3⟩, -⟩ := h
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (statOf q.sch.mr) - BitVec.ofNat 64 1 ∧
      t.mem = s.mem) (by brun [h3]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3', hm⟩, k⟩ =>
      ⟨⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hO,
        by rw [hm]; exact hK, by rw [hm]; exact hU, ho.congr k.wr, by rw [hm]; exact hS⟩, h3'⟩

/-! ## From `TS` -/

theorem ts_ms0 {q : FPub} {s : State} (h : TS q s) : MS0 q.L s := by
  obtain ⟨⟨-, hdm, hws, -, -, pB, r, hc, -⟩, -⟩ := h
  exact ⟨hws, hdm.w4, hdm.w64, _, hc,
    VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * q.w) (by have := hdm.w4; omega) _⟩

/-- `montSetup` leaves what Miller–Rabin needs, with the shape of its result. -/
theorem ms_mrpre (M : Mont) {q : FPub} {s : State} (h : TS q s) : WP isa (seqs (montSetup M.mm)) s (MrPre q) := by
  obtain ⟨⟨hwr, hdm, hws, hh, ho, pB, r, hc, -, -, hsrc, -, hrl, hS⟩, hcl, hco, hgb⟩ := h
  have hw4 := hdm.w4
  have hw64 := hdm.w64
  have h64 : 8 * (8 * q.w) = 64 * q.w := by omega
  generalize hcd : Spec.RsaKeyGen.candidate (64 * q.w) (Spec.Rsa.os2ip (r.take (8 * q.w))) = c at hc
  have hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c := hcd ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega) _
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  have htop : 2 ^ (64 * q.w - 1) ≤ c := by
    have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    omega
  have hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * q.w - 1) :=
      Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * q.w - 1 by omega))
    omega
  -- The shape of the test's result.
  have e1 := VG.Proof.RsaKeyGen.sched_close (8 * q.w) (Spec.Rsa.os2ip q.eB) (Spec.RsaKeyGen.otherPrime pB) r
  rw [hS, hcl, h64, hcd] at e1
  have e2 := VG.Proof.RsaKeyGen.sched_comp (e := Spec.Rsa.os2ip q.eB) (r := r) (by rw [h64, hcd]; exact e1.symm)
  rw [hS, hco, h64, hcd] at e2
  have e3 := VG.Proof.RsaKeyGen.sched_gbad (e := Spec.Rsa.os2ip q.eB) (r := r) (by rw [h64, hcd]; exact e1.symm)
    (by rw [h64, hcd]; exact e2.symm)
  rw [hS, hgb, h64, hcd] at e3
  have e4 := VG.Proof.RsaKeyGen.sched_mr (e := Spec.Rsa.os2ip q.eB) (r := r) (by rw [h64, hcd]; exact e1.symm)
    (by rw [h64, hcd]; exact e2.symm) (by rw [h64, hcd]; exact e3.symm)
  rw [hS, h64, hcd] at e4
  have hres : mrRest c (checksW q.w) r 1 0 (8 * q.w) = Spec.RsaKeyGen.primalityTest c (r.drop (8 * q.w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega) ⟨hodd, hlo, hhi⟩,
      VG.Proof.RsaKeyGen.checksW_eq q.w (by omega) hw4]
  have hnw := hws.scr.nowrap
  have hZ := hws.hZ
  have hZ' : 256 + 16 * (8 * (q.w + 2)) ≤ q.Z := by simpa only [slot, hdrBytes] using hZ
  refine WP.mono (montSetup_ok M hws hw4 hw64 hc hodd htop)
    fun t ⟨h₁, hinv₁, hn₁, hr2₁, hr1₁, hrm₁, hch₁, f₁, k₁⟩ => ?_
  have hW : ∀ {i : Nat}, i < 32 → (∀ r ∈ msRanges q.w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i) →
      word t.mem q.B (8 * i) = word s.mem q.B (8 * i) :=
    fun _ hd => f₁.word_eq hd (by have := hws.h256; omega)
  have hsl₁ : ∀ r ∈ msRanges q.w, r.1 + r.2 ≤ q.Z := by kt_disj
  have hin₁ : InScr q.B q.Z s.mem t.mem := InScr.of_frm f₁ (fun r hr => by have := hsl₁ r hr; omega)
  refine ⟨hw4, hw64, hdm.rl, c, _, r, ⟨h₁, hinv₁, hn₁, rfl, hr1₁, hrm₁⟩, hr2₁, hc1, ⟨hodd, hlo, hhi⟩,
    (hW (by decide) (by kt_disj)).trans hh.rand, by rw [(hW (by decide) (by kt_disj)).trans hh.rlen, hrl], hrl, hch₁,
    hsrc.congrK hin₁ k₁, (hW (by decide) (by kt_disj)).trans hh.used, by rw [hrl]; exact hdm.rk,
    by rw [hres, e4], (hW (by decide) (by kt_disj)).trans hh.out, (hW (by decide) (by kt_disj)).trans hh.usedP,
    (hW (by decide) (by kt_disj)).trans hh.len, ho.congr k₁.wr⟩

/-- The tail of a candidate, from `montSetup` to the result, leaks the same
in runs related by `TS`. -/
theorem kTail_ct (M : Mont) :
    RelCT isa (Two TS) (seqs (montSetup M.mm ++ millerRabin M.mm ++ [mrResult])) fun _ _ => True := by
  rw [List.append_assoc]
  exact ct_app' (by simp [montSetup]) (by simp [millerRabin])
    (two_post (two_map FPub.L (fun _ _ h => ts_ms0 h) (montSetup_ct M)) fun _ _ h => ms_mrpre M h)
    (ct_app' (by simp [millerRabin]) (by simp)
      ((millerRabin_ct M).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => loopEnd_endq h) h)
      mrResult_ct)

end VG.Proof.RsaKeyGen.AArch64
