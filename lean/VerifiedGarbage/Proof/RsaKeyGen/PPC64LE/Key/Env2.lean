module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLoop
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on PPC64LE: the flags, the comparisons, the division and the inverse as values

The blocks on the flag slots (`bitOf`, `andS`, `notS`, `andNotS`, `selS`) and
on a digit (`setDigit`), with a continuation; `ltSE` (a comparison, through
`aT`), `addToE` (a sum), `divE` (the division through `aDv`) and `invOfE`
(`invOf`: the inverse and the gcd).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel half eqS bitOf andS stBorrow inverse aM aNM aZero aT1
  aT3 aT4 sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.Div (div)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aOne X0 X1 X2 X3 X4 X5 X6 X7 X8 notS andNotS selS setDigit
  ltS addTo invOf)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-! ## Slots -/

/-- `KS` after a write of the flag `d`. -/
theorem KS.flag {m m' : Mem} {B : Addr} {w : Nat} {V F : Nat → Nat} (h : KS m B w V F) {d x : Nat}
    (k : KeyWorkspace.Keep B w [] [d] m m') (hd : d ∈ flags) (v : slot m' B d = x)
    (fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64) : KS m' B w V (upd F d x) :=
  h.step k fit (fun _ _ _ => rfl) (fun j hj => by simp at hj) (fun e _ hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; rw [upd_ne hn])
    (fun e he _ => by simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rw [he, upd_self, v])
    (fun hj => by simp at hj) (by simpa using flag_hdr d hd) (flag_sep d hd)

/-- `KS` after writes of the slots the shared routines use. -/
theorem KS.shared {m m' : Mem} {B : Addr} {w : Nat} {V F : Nat → Nat} (h : KS m B w V F)
    (k : KeyWorkspace.Keep B w [] [sOdd, sB, sC] m m') (fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64) :
    KS m' B w V F :=
  h.step k fit (fun _ _ _ => rfl) (fun j hj => by simp at hj) (fun _ _ _ => rfl)
    (fun e he hf => by simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                       rcases he with rfl | rfl | rfl <;> simp [flags, X0, X1, X2, X3, X4, X5, X6, X7, X8, sOdd,
                         sB, sC] at hf)
    (fun hj => by simp at hj)

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem flag_kk {d : Nat} (hd : d ∈ flags) : ∀ x ∈ [d], x ∈ allSlots := by
  simpa using flag_slot d hd

/-- `bitOf d j`. -/
theorem bitOfE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d j : Nat} (hj : j < nArr := by decide)
    (hd : d ∈ flags := by decide) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w nArr → KS t.mem B w V (upd F d (V j % 2)) → KK B w s.mem t.mem →
      Keep opsRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf d j ++ rest)) s Q :=
  bitOf_ok h hj nArr_le (flag_hdr d hd) fun t ht kt v kr =>
    k t ht (ks.flag kt hd (by rw [v, ks.arrs j hj]) (fit_of h)) (KK.of kt (by simp) (flag_kk hd)) kr.mono

/-- `andS d a b`. -/
theorem andSE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d a b : Nat} (hd : d ∈ flags := by decide)
    (ha : a ∈ flags := by decide) (hb : b ∈ flags := by decide) (ba : F a ≤ 1) (bb : F b ≤ 1)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w nArr → KS t.mem B w V (upd F d (if F a = 1 ∧ F b = 1 then 1 else 0)) →
      KK B w s.mem t.mem → Keep opsRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (andS d a b ++ rest)) s Q := by
  rw [← ks.flg a ha] at ba k
  rw [← ks.flg b hb] at bb k
  exact andS_ok h (flag_hdr d hd) (flag_hdr a ha) (flag_hdr b hb) ba bb fun t ht kt v kr =>
    k t ht (ks.flag kt hd v (fit_of h)) (KK.of kt (by simp) (flag_kk hd)) kr.mono

/-- `notS d a`. -/
theorem notSE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d a : Nat} (hd : d ∈ flags := by decide)
    (ha : a ∈ flags := by decide) (ba : F a ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w nArr → KS t.mem B w V (upd F d (1 - F a)) → KK B w s.mem t.mem →
      Keep opsRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (notS d a ++ rest)) s Q := by
  rw [← ks.flg a ha] at ba k
  exact notS_ok h (flag_hdr d hd) (flag_hdr a ha) ba fun t ht kt v kr =>
    k t ht (ks.flag kt hd v (fit_of h)) (KK.of kt (by simp) (flag_kk hd)) kr.mono

/-- `andNotS d a b`. -/
theorem andNotSE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d a b : Nat} (hd : d ∈ flags := by decide)
    (ha : a ∈ flags := by decide) (hb : b ∈ flags := by decide) (ba : F a ≤ 1) (bb : F b ≤ 1)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w nArr → KS t.mem B w V (upd F d (if F a = 0 ∧ F b = 1 then 1 else 0)) →
      KK B w s.mem t.mem → Keep opsRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (andNotS d a b ++ rest)) s Q := by
  rw [← ks.flg a ha] at ba k
  rw [← ks.flg b hb] at bb k
  exact andNotS_ok h (flag_hdr d hd) (flag_hdr a ha) (flag_hdr b hb) ba bb fun t ht kt v kr =>
    k t ht (ks.flag kt hd v (fit_of h)) (KK.of kt (by simp) (flag_kk hd)) kr.mono

/-- `selS d a b c`. -/
theorem selSE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d a b c : Nat} (hd : d ∈ flags := by decide)
    (ha : a ∈ flags := by decide) (hb : b ∈ flags := by decide) (hc : c ∈ flags := by decide)
    (ba : F a ≤ 1) (bb : F b ≤ 1) (bc : F c ≤ 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w nArr → KS t.mem B w V (upd F d (if F c = 1 then F b else F a)) →
      KK B w s.mem t.mem → Keep opsRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (selS d a b c ++ rest)) s Q := by
  rw [← ks.flg a ha] at ba k
  rw [← ks.flg b hb] at bb k
  rw [← ks.flg c hc] at bc k
  exact selS_ok h (flag_hdr d hd) (flag_hdr a ha) (flag_hdr b hb) (flag_hdr c hc) ba bb bc
    fun t ht kt v kr => k t ht (ks.flag kt hd v (fit_of h)) (KK.of kt (by simp) (flag_kk hd)) kr.mono

/-- A number below `2^(32 k)` has a zero digit `k`. -/
theorem digit_zero {m : Mem} {B : Addr} {w j k : Nat} (hk : k < w) (hv : num m B w j < 2 ^ (32 * k)) :
    w32 m B (arr w j + 4 * k) = 0 := by
  have e := val32_split m B (arr w j) hk
  change val32 m B (arr w j) w < _ at hv
  rcases Nat.eq_zero_or_pos (w32 m B (arr w j + 4 * k)) with z | z
  · exact z
  · have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * w32 m B (arr w j + 4 * k) := Nat.le_mul_of_pos_right _ z
    omega

/-- `setDigit j x`, the byte offset `4 k` in `r6`, for a number below `2^(32 k)`. -/
theorem setDigitE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {j x k : Nat} (hj : j < nArr := by decide)
    (hjdv : j ≠ aDv := by decide) (hx : x < 2 ^ 15) (hk : k < w) (h6 : s.gpr .r6 = BitVec.ofNat 64 (4 * k))
    (hv : V j < 2 ^ (32 * k)) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, Ws t B Z w nArr → KS t.mem B w (upd V j (V j + 2 ^ (32 * k) * x)) F →
      KK B w s.mem t.mem → Keep opsRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setDigit j x ++ rest)) s Q := by
  refine setDigit_ok h hj nArr_le hx hk h6 fun t ht kt v kr _ => kk t ht ?_ (KK.of kt (arr_mem hj) (by simp))
    kr.mono
  rw [digit_zero hk (by rw [ks.arrs j hj]; exact hv), Nat.mul_zero, Nat.add_zero, ks.arrs j hj] at v
  refine ks.step kt (fit_of h) (fun i hi hn => ?_) (fun i hi => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi, upd_self, v]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hjdv

/-! ## Comparisons and sums -/

/-- `ltS d a b`: the flag `d` := `[a] < [b]`, through `aT`. -/
theorem ltSE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {d a b : Nat} (ha : a < nArr := by decide)
    (hb : b < nArr := by decide) (haT : aT ≠ a := by decide) (hbT : aT ≠ b := by decide)
    (hd : d ∈ flags := by decide) :
    WP isa (seqs (ltS d a b)) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V aT (subW w (V a) (V b))) (upd F d (if V a < V b then 1 else 0)) ∧
      KK B w s.mem t.mem ∧ Keep opsRegs s t := by
  change WP isa (.seq (sub3 aT a b) (.block (stBorrow d))) s _
  rw [WP.seq_iff]
  refine WP.mono (sub3E h ks (o := aT) (a := a) (b := b) (by decide) ha hb haT hbT (by decide)) fun t ⟨ht, kt, b9, kk, kr⟩ => ?_
  rw [← List.append_nil (stBorrow d)]
  refine stBorrow_ok ht (flag_hdr d hd) (by rw [b9]; split <;> omega) fun u hu ku v ru => WP.block_nil ?_
  exact ⟨hu, kt.flag ku hd (by rw [v, b9]) (fit_of ht), kk.trans (KK.of ku (by simp) (flag_kk hd)),
    kr.trans' ru.mono⟩

/-- `addTo o a n z`: `[o] := [o] + [a]` modulo `2^(32 w)`, through `n`, for `[z] = 0`. -/
theorem addToE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o a n z : Nat} (ho : o < nArr := by decide)
    (ha : a < nArr := by decide) (hn : n < nArr := by decide) (hz : z < nArr := by decide)
    (hon : o ≠ n := by decide) (hna : n ≠ a := by decide) (hnz : n ≠ z := by decide)
    (hodv : o ≠ aDv := by decide) (hndv : n ≠ aDv := by decide) (z0 : V z = 0) :
    WP isa (addTo o a n z) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd (upd V n (subW w 0 (V a))) o ((V o + V a) % 2 ^ (32 * w))) F ∧
      KK B w s.mem t.mem ∧ Keep opsRegs s t := by
  rw [addTo, WP.seq_iff]
  refine WP.mono (sub3E h ks (o := n) (a := z) (b := a) hn hz ha hnz hna hndv) fun t ⟨ht, kt, _, kk, kr⟩ => ?_
  refine WP.mono (sub3SelfE ht kt (o := o) (b := n) ho hn hon hodv) fun u ⟨hu, ku, kk', kr'⟩ =>
    ⟨hu, ?_, kk.trans kk', kr.trans' kr'⟩
  have e : upd (upd V n (subW w (V z) (V a))) o (subW w (upd V n (subW w (V z) (V a)) o)
      (upd V n (subW w (V z) (V a)) n)) = upd (upd V n (subW w 0 (V a))) o ((V o + V a) % 2 ^ (32 * w)) := by
    rw [upd_ne hon, upd_self, z0, subW_neg (ks.lt ha)]
  exact e ▸ ku

/-! ## The division -/

/-- `div q r aDv t`: `[q] := [q] / [aDv]`, `[r] := [q] mod [aDv]` (for a
nonzero divisor), and `[t]` scratch. -/
theorem divE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {q r t : Nat} (hq : q < nArr := by decide)
    (hr : r < nArr := by decide) (ht : t < nArr := by decide) (hqr : q ≠ r := by decide)
    (hqt : q ≠ t := by decide) (hrt : r ≠ t := by decide) (hqd : q ≠ aDv := by decide)
    (hrd : r ≠ aDv := by decide) (htd : t ≠ aDv := by decide) :
    WP isa (div q r aDv t) s fun u => Ws u B Z w nArr ∧
      (∃ V', KS u.mem B w V' F ∧ (∀ j < nArr, j ≠ q → j ≠ r → j ≠ t → V' j = V j) ∧
        (0 < V aDv → V' q = V q / V aDv ∧ V' r = V q % V aDv)) ∧
      KK B w s.mem u.mem ∧ Keep opsRegs s u := by
  refine WP.mono (div_ok h hq hr (by decide) ht nArr_le hqr hqd hqt hrd hrt (Ne.symm htd) ks.dv)
    fun u ⟨hu, ku, kr, v⟩ => ⟨hu, ⟨fun j => num u.mem B w j, ?_, fun j hj a b c => ?_, fun hd => ?_⟩,
      KK.of ku (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                   rcases hj with rfl | rfl | rfl <;> exact List.mem_range.mpr ‹_›) (by simp), kr.mono⟩
  · refine ks.step ku (fit_of h) (fun j hj hn => ?_) (fun j _ => rfl) (fun _ _ _ => rfl)
      (fun d hd => by simp at hd) (fun hd => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [← ks.arrs j hj]
      exact ku.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by simp) (fit_of h j hj)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with e | e | e <;> [exact absurd e.symm hqd; exact absurd e.symm hrd; exact absurd e.symm htd]
  · rw [← ks.arrs j hj]
    exact ku.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by simp) (fit_of h j hj)
  · rw [← ks.arrs aDv (by decide)] at hd
    obtain ⟨e1, e2⟩ := v hd
    rw [← ks.arrs aDv (by decide), ← ks.arrs q hq]
    refine ⟨e1, ?_⟩
    have hl : num1 u.mem B w r < 2 ^ (32 * w) := by
      rw [e2]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_lt (val32_lt _ _ _ _))
    exact (VG.Proof.Rsa.PPC64LE.CrtValues.num_of_num1 hl).trans e2

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
