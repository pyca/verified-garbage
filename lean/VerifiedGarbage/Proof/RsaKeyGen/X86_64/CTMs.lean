import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrLoop

/-!
# A candidate on x86-64: constant time of `montSetup`

`-c⁻¹`, `R² mod c` (doublings, then squarings), `R mod c` and `c − R mod c`,
then the number of uniform witnesses. Between the pieces each run keeps
`Good` (whose header words `w` and the bases are all its pieces read) and
enough for the multiplications to run (`MsMid`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The header words `Good` fixes. -/
def gvs (B : Addr) (w : Nat) : List (Nat × BitVec 64) :=
  [(sW, BitVec.ofNat 64 w), (sArr 0, off B (slot w 0)), (sArr 1, off B (slot w 1)), (sArr 2, off B (slot w 2)),
    (sArr 3, off B (slot w 3)), (sArr 4, off B (slot w 4)), (sArr 5, off B (slot w 5)), (sArr 6, off B (slot w 6)),
    (sArr 7, off B (slot w 7))]

def gS : List Nat := [sW, sArr 0, sArr 1, sArr 2, sArr 3, sArr 4, sArr 5, sArr 6, sArr 7]

theorem gvs_fst (B : Addr) (w : Nat) : (gvs B w).map (·.1) = gS := rfl

theorem good_hp {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {wr : List Region} (hg : Good s B Z w mi)
    (hw : s.wr = wr) : HP B wr (gvs B w) s := by
  refine ⟨hg.rdi, hw, fun e he => ?_⟩
  simp only [gvs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.hdr.hw
  all_goals exact hg.hdr.harr _ (by decide)

/-- The public data of the end of a candidate: the working space, the
writable regions, the header words Miller–Rabin keeps, and the shape of its
result. -/
structure TPub where
  B : Addr
  Z : Nat
  w : Nat
  wr : List Region
  op : Addr
  up : Addr
  rP : Addr
  rl : Nat
  S : Option (Bool × Nat)

/-- Miller–Rabin's public data. -/
abbrev TPub.lp (q : TPub) : LPub :=
  ⟨⟨q.B, q.Z, q.w, q.wr, q.op, q.up, q.rP, q.rl, Proof.RsaKeyGen.checksW q.w⟩, 8 * q.w, q.S⟩

/-- The bounds of the working space. -/
structure TDims (q : TPub) : Prop where
  z : slot q.w 8 ≤ q.Z
  x : slot q.w aRm1 + 8 * (q.w + 2) ≤ q.Z
  w4 : 4 ≤ q.w
  w64 : q.w ≤ 64

theorem TDims.mr {q : TPub} (h : TDims q) : MrDims q.B q.Z q.w := ⟨h.z, h.x, h.w4, h.w64⟩

/-- `Good`, in the writable regions. -/
def GW (q : TPub) (s : State) : Prop :=
  KW q.B q.wr ∧ s.wr = q.wr ∧ TDims q ∧ ∃ mi, Good s q.B q.Z q.w mi

theorem GW.goodW {q : TPub} {s : State} (h : GW q s) : GoodW ⟨q.B, q.Z, q.w⟩ s :=
  let ⟨_, _, hd, mi, hg⟩ := h; ⟨mi, hg, hd.z⟩

theorem GW.hp {q : TPub} {s : State} (h : GW q s) : KW q.B q.wr ∧ HP q.B q.wr (gvs q.B q.w) s :=
  let ⟨hk, hw, _, _, hg⟩ := h; ⟨hk, good_hp hg hw⟩

/-- Between the squarings: `-c⁻¹`, the number 1, and `[aR2] < c`. -/
def MsMid (q : TPub) (s : State) : Prop :=
  GW q s ∧ ∃ (mi : BitVec 64) (N : Nat), Good s q.B q.Z q.w mi ∧
    ((word s.mem q.B (slot q.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧ wv s.mem q.B (slot q.w aN) q.w = N ∧ 1 < N ∧
    wv s.mem q.B (slot q.w aOne) q.w = 1 ∧ wv s.mem q.B (slot q.w aR2) q.w < N

/-- A multiplication `o := a b` keeps what `MsMid` needs but `[aR2] < c`, and
gives `[o] < c`. -/
theorem msMid_mm (M : Mont) {q : TPub} {s : State} {o a b : Nat} (hp : GW q s) {mi : BitVec 64} {N : Nat}
    (hg : Good s q.B q.Z q.w mi) (hinv : ((word s.mem q.B (slot q.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (hn : wv s.mem q.B (slot q.w aN) q.w = N) (ho : o < 8) (ha : a < 8) (hb : b < 8) (d1 : o ≠ aAcc) (d2 : o ≠ aTmp)
    (d3 : a ≠ aAcc) (d4 : b ≠ aAcc) (d5 : a ≠ aTmp) (d6 : b ≠ aTmp) (d7 : o ≠ aN)
    (hB : wv s.mem q.B (slot q.w b) q.w < N) :
    WP isa (M.mm o a b) s fun t => GW q t ∧ Good t q.B q.Z q.w mi ∧
      ((word t.mem q.B (slot q.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧ wv t.mem q.B (slot q.w aN) q.w = N ∧
      wv t.mem q.B (slot q.w o) q.w < N ∧ Arrays q.B q.w [aAcc, aTmp, o] s.mem t.mem := by
  obtain ⟨hk, hw, hd, -⟩ := hp
  have hn' : q.B.toNat + slot q.w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; have := hd.z; omega
  have hnm : aN ∉ [aAcc, aTmp, o] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, fun h => d7 h.symm⟩
  refine WP.mono (M.mm_ok hg hd.z (by have := hd.w4; omega) (by have := hd.w64; omega) ho ha hb d1 d2 d3 d4 hinv
    (by rw [hn]; exact hB) d5 d6) fun t ⟨hg', hlt, _, ha', k⟩ => ⟨⟨hk, k.2.2.trans hw, hd, mi, hg'⟩, hg', ?_, ?_, ?_, ha'⟩
  · rw [ha'.word0_of_not_mem (by decide) hnm hn' (by have := hd.w4; omega)]; exact hinv
  · rw [ha'.wv_of_not_mem (by decide) hnm hn']; exact hn
  · rw [← hn]; exact hlt

/-- A squaring of `[aR2]` leaks the same in runs that agree on the public
data, and keeps `MsMid`. -/
theorem sq_ct (M : Mont) : RelCT isa (Two MsMid) (M.mm aR2 aR2 aR2) (Two MsMid) := by
  refine two_post (two_map (fun q : TPub => (⟨q.B, q.Z, q.w⟩ : Ws)) (fun _ _ h => h.1.goodW)
    (M.ct (Or.inl ⟨rfl, rfl, rfl⟩))) ?_
  rintro q s ⟨hp, mi, N, hg, hinv, hn, hN1, hone, hlt⟩
  exact WP.mono (msMid_mm M hp hg hinv hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hlt) fun t ⟨hp', hg', hinv', hn', hlt', ha⟩ =>
    ⟨hp', mi, N, hg', hinv', hn', hN1, by
      rw [ha.wv_of_not_mem (by decide) (by decide) (by have := hg.scr.nowrap; have := hp.2.2.1.z; omega)]; exact hone,
      hlt'⟩

theorem sqs_ct' (M : Mont) (n : Nat) :
    RelCT isa (Two MsMid) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2))) (Two MsMid) := by
  induction n with
  | zero => exact sq_ct M
  | succ n ih => exact RelCT.seq (sq_ct M) ih

theorem eval_ne_count' {s : State} {j n : Nat} (hj : j < n) (hz : s.zf = some (decide (j + 1 = n))) :
    isa.eval .ne s = some (decide (j + 1 < n)) := by
  simp only [eval, hz, Option.map_some, Option.some.injEq]
  by_cases h : j + 1 = n
  · simp [h]
  · simp only [h, decide_false, Bool.not_false]; exact (decide_eq_true (by omega)).symm

/-- After `j` of the `w + 1` doublings. -/
def DbW (q : TPub) (j : Nat) (s : State) : Prop :=
  KW q.B q.wr ∧ TDims q ∧ ∃ (mi : BitVec 64) (s₀ : State) (O N : Nat),
    DblsInv s₀ q.B q.Z q.w mi aN aAcc aTmp aR2 kT0 (q.w + 1) O N j s ∧ s₀.wr = q.wr ∧ 1 < N ∧
    ((word s₀.mem q.B (slot q.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧ wv s₀.mem q.B (slot q.w aOne) q.w = 1

theorem dbW_gw {q : TPub} {j : Nat} {s : State} (h : DbW q j s) : GW q s :=
  let ⟨hk, hd, mi, _, _, _, hI, hw, _⟩ := h; ⟨hk, hI.keep.2.2.trans hw, hd, mi, hI.scr, hI.rdi, hI.hdr⟩

/-- The doublings leak the same in runs that agree on the public data. -/
theorem doubles_ct' : RelCT isa (Two fun q s => MsMid q s ∧ s.gpr .rcx = BitVec.ofNat 64 (q.w + 1))
    (doubles aN aAcc aTmp aR2 kT0) (Two MsMid) := by
  rw [doubles_eq]
  refine RelCT.seq (kt_piece (fun q : TPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
    (fun q => gvs_fst _ _) (fun _ _ h => h.1.1.hp) (pins_nil _) (by taint_decide) ?_)
    ((two_loop (Φ := DbW) (Ψ := fun q s => DbW q (q.w + 1) s) (fun q => q.w + 1) ?_ ?_).mono (fun _ _ h => h)
      fun _ _ h => two_mono (Φ := fun q s => DbW q (q.w + 1) s) ?_ h)
  · rintro q s ⟨⟨⟨hk, hw, hd, -⟩, mi, N, hg, hinv, hn, hN1, hone, hlt⟩, hcx⟩
    exact WP.mono (dblStart_ok hg.scr hg.rdi hg.hdr hd.z (mo := aN) (o := aR2) (acc := aAcc) (tmp := aTmp)
      (by decide) (by decide) (by decide) (by decide) hcx (by rw [hn]; exact hlt))
      fun t hI => ⟨by omega, hk, hd, mi, s, _, _, hI, hw, by rw [hn]; exact hN1, hinv, hone⟩
  · refine RelCT.seq (R := Two fun (p : TPub × Nat) s => KW p.1.B p.1.wr ∧ HP p.1.B p.1.wr [] s)
      (kt_piece (fun p : TPub × Nat => p.1.B) (fun p => p.1.wr) gS (fun p => gvs p.1.B p.1.w) [] (by decide)
        (fun p => gvs_fst _ _) (fun _ _ h => (dbW_gw h.2).hp) (pins_nil _) (by taint_decide) ?_)
      (kt_ct (fun p : TPub × Nat => p.1.B) (fun p => p.1.wr) [] (fun _ => []) [] (by decide) (fun _ => rfl)
        (fun _ _ h => h) (pins_nil _) (by taint_decide))
    rintro ⟨q, j⟩ s ⟨hj, hk, hd, mi, s₀, O, N, hI, hw, hN1, -⟩
    have hw' : q.w < 2 ^ 31 := by have := hd.w64; dsimp only at this; omega
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hd.z (by have := hd.w4; omega) hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ (by omega))) fun t ⟨_, _, k⟩ =>
        ⟨hk, (k.gpr (by decide)).trans hI.rdi, k.2.2.trans (hI.keep.2.2.trans hw), fun _ he => absurd he List.not_mem_nil⟩
  · rintro q j s hj ⟨hk, hd, mi, s₀, O, N, hI, hw, hN1, hinv, hone⟩
    have hw' : q.w < 2 ^ 31 := by have := hd.w64; omega
    exact WP.mono (dblIter_ok (c := q.w + 1) (O := O) (N := N) hd.z (by have := hd.w4; omega) hw' (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (show q.w + 1 < 2 ^ 31 by have := hd.w64; omega) (show 0 < N by omega) hj hI) fun t ⟨hz, hI'⟩ => ⟨eval_ne_count' hj hz, fun _ => ⟨hk, hd, mi, s₀, O, N, hI', hw, hN1, hinv, hone⟩,
        fun e => e ▸ ⟨hk, hd, mi, s₀, O, N, hI', hw, hN1, hinv, hone⟩⟩
  · rintro q s ⟨hk, hd, mi, s₀, O, N, hI, hw, hN1, hinv, hone⟩
    have hn := hI.scr.nowrap
    have hz := hd.z
    have harr : ∀ {j : Nat}, j < 8 → j ≠ aAcc → j ≠ aTmp → j ≠ aR2 → ∀ r ∈ [(slot q.w aAcc, 8 * (q.w + 2)),
        (slot q.w aTmp, 8 * (q.w + 2)), (slot q.w aR2, 8 * (q.w + 2)), (8 * kT0, 8)],
        slot q.w j + 8 * (q.w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot q.w j := by
      intro j hj h1 h2 h3
      have := hdr_lt_slot q.w j (show kT0 < 32 by decide)
      have s1 := slot_sep (w := q.w) h1
      have s2 := slot_sep (w := q.w) h2
      have s3 := slot_sep (w := q.w) h3
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> omega
    have sN := slot_le (w := q.w) (show aN < 8 by decide)
    have sO := slot_le (w := q.w) (show aOne < 8 by decide)
    refine ⟨⟨hk, hI.keep.2.2.trans hw, hd, mi, hI.scr, hI.rdi, hI.hdr⟩, mi, N, ⟨hI.scr, hI.rdi, hI.hdr⟩, ?_, hI.nv,
      hN1, ?_, by rw [hI.ov, ← hI.nv]; exact Nat.mod_lt _ (by rw [hI.nv]; omega)⟩
    · rw [hI.frm.word_eq (fun r hr => by
        have := harr (show aN < 8 by decide) (by decide) (by decide) (by decide) r hr; omega) (by omega)]; exact hinv
    · rw [hI.frm.wv_eq (fun r hr => by
        have := harr (show aOne < 8 by decide) (by decide) (by decide) (by decide) r hr; omega) (by omega)]; exact hone

/-- What `montSetup` needs, and what `millerRabin` will. -/
def MsPre (q : TPub) (s : State) : Prop :=
  GW q s ∧ q.rl < 2 ^ 64 ∧ ∃ (mi : BitVec 64) (c : Nat) (r : List Byte), Good s q.B q.Z q.w mi ∧
    wv s.mem q.B (slot q.w aN) q.w = c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c ∧
    word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kUsedP) = q.up ∧ word s.mem q.B (8 * kRand) = q.rP ∧
    word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) ∧ word s.mem q.B (8 * kRandLen) = BitVec.ofNat 64 r.length ∧
    word s.mem q.B (8 * kUsed) = BitVec.ofNat 64 (8 * q.w) ∧ Src s q.B q.Z q.rP r ∧ r.length = q.rl ∧
    8 * q.w ≤ r.length ∧ VG.Proof.RsaKeyGen.shapeOf (mrRest c (Proof.RsaKeyGen.checksW q.w) r 1 0 (8 * q.w)) = q.S

theorem montSetup_eq' (mul : Nat → Nat → Nat → Prog isa) : montSetup mul =
    [.block (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .r10))] :
      List Instr) ++ minv ++ ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
      setWord aOne .rcx,
      .block [.movImm64 .rdx (BitVec.ofNat 64 (2 ^ 63)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
      setWord aR2 .rcx,
      .block [.mov .rcx (.mem (hdr sW)), .alu .add .rcx (.imm 1)]] ++
    ([doubles aN aAcc aTmp aR2 kT0] ++ (List.replicate (5 + 1) (mul aR2 aR2 aR2) ++ ([mul aY aR2 aOne] ++
    ([.block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY)))] ++ extBase aR1 .rbx), copyWords] ++
    ([.block ([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] ++ extBase aR1 .r10 ++
        extBase aRm1 .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        .store (ix .rsi .r14) .rax, cfToRbp]] ++
    [.block [.mov .rcx (.mem (hdr sW)), .mov32 .rax (.imm 27), .alu .cmp .rcx (.imm 5)],
      .ite .b (.block []) (seqs [
        .block [.mov32 .rax (.imm 8), .alu .cmp .rcx (.imm 6)],
        .ite .b (.block []) (seqs [
          .block [.mov32 .rax (.imm 7), .alu .cmp .rcx (.imm 7)],
          .ite .b (.block []) (seqs [
            .block [.mov32 .rax (.imm 6), .alu .cmp .rcx (.imm 8)],
            .ite .b (.block []) (seqs [
              .block [.mov32 .rax (.imm 5), .alu .cmp .rcx (.imm 22)],
              .ite .b (.block []) (seqs [
                .block [.mov32 .rax (.imm 4), .alu .cmp .rcx (.imm 59)],
                .ite .b (.block []) (.block [.mov32 .rax (.imm 3)])])])])])]),
      .block [.store (hdr kChecks) .rax]]))))) := rfl

/-- After `R mod c`. -/
def MsY (q : TPub) (j : Nat) (s : State) : Prop :=
  GW q s ∧ ∃ (mi : BitVec 64) (N : Nat), Good s q.B q.Z q.w mi ∧ wv s.mem q.B (slot q.w aN) q.w = N ∧
    wv s.mem q.B (slot q.w j) q.w < N

theorem msRanges_hdr (w : Nat) : ∀ k ∈ [kOut, kUsedP, kRand, kLen, kRandLen, kUsed],
    ∀ r ∈ msRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [msRanges]; rng_disj

/-- `montSetup` leaks the same in runs that agree on the public data. -/
theorem montSetup_ct (M : Mont) :
    RelCT isa (Two MsPre) (seqs (montSetup M.mm)) (Two fun (q : TPub) s => MrPre q.lp s) := by
  rw [montSetup_eq']
  refine two_post ?_ ?_
  refine RelCT.seqs_app (by simp) (by simp)
    (RelCT.seq (R := Two fun q s => MsMid q s ∧ s.gpr .rcx = BitVec.ofNat 64 (q.w + 1)) ?_ ?_)
  rotate_left
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq doubles_ct' ?_)
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (sqs_ct' M 5) ?_)
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two fun q s => MsY q aY s) ?_ ?_)
  rotate_left
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two fun q s => MsY q aR1 s) ?_ ?_)
  rotate_left
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two GW) ?_ ?_)
  rotate_left
  rotate_left
  rotate_left
  · -- `-c⁻¹`, the number 1, and the start of `R²`.
    refine kt_piece (fun q : TPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
      (fun q => gvs_fst _ _) (fun _ _ h => h.1.hp) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨⟨hk, hw, hd, -⟩, -, mi, c, r, hg, hn, hsh, -⟩
    obtain ⟨hodd, hlo, hhi⟩ := hsh
    have hw4 := hd.w4
    have e : 2 ^ (64 * q.w - 2) * 4 = 2 ^ 63 * 2 ^ (64 * (q.w - 1)) * 2 := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_succ]; congr 1; omega
    have hp : 0 < 2 ^ (64 * q.w - 2) := Nat.two_pow_pos _
    exact WP.mono (msFront_ok hg hd.z hw4 hd.w64 hn hodd) fun t ⟨mi', hg', hinv, hn', hone, hr2, hcx, hwt⟩ =>
      ⟨⟨⟨hk, hwt.trans hw, hd, mi', hg'⟩, mi', c, hg', hinv, hn', by omega, hone, by rw [hr2]; omega⟩, hcx⟩
  · -- `R mod c`.
    refine two_post (two_map (fun q : TPub => (⟨q.B, q.Z, q.w⟩ : Ws)) (fun _ _ h => h.1.goodW)
      (M.ct (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))) ?_
    rintro q s ⟨hp, mi, N, hg, hinv, hn, hN1, hone, -⟩
    exact WP.mono (msMid_mm M hp hg hinv hn (o := aY) (a := aR2) (b := aOne) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hone]; exact hN1))
      fun t ⟨hp', hg', _, hn', hlt, _⟩ => ⟨hp', mi, N, hg', hn', hlt⟩
  · -- `[aR1] := R mod c`.
    refine kt_piece (fun q : TPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
      (fun q => gvs_fst _ _) (fun _ _ h => h.1.hp) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨⟨hk, hw, hd, -⟩, mi, N, hg, hn, hlt⟩
    have hnw := hg.scr.nowrap
    have sN := slot_le (w := q.w) (show aN < 8 by decide)
    have hz := hd.z
    exact WP.mono (copyToExt_ok hg hd.z (by have := hd.w4; omega) (by have := hd.w64; omega) (a := aY) (d := aR1)
      (by decide) (by decide) (by have := hd.x; unfold slot aR1 aRm1 at *; omega)) fun t ⟨hv, ho, k⟩ =>
      ⟨⟨hk, k.2.2.trans hw, hd, mi, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
        Hdr.outside hg.hdr ho (by unfold slot; omega)⟩, mi, N, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
        Hdr.outside hg.hdr ho (by unfold slot; omega)⟩,
        by rw [ho.wv (Or.inl (by unfold slot aR1 aN; omega)) (by omega)]; exact hn, by rw [hv]; exact hlt⟩
  · -- `[aRm1] := c − R mod c`.
    refine kt_piece (fun q : TPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
      (fun q => gvs_fst _ _) (fun _ _ h => h.1.hp) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨⟨hk, hw, hd, -⟩, mi, N, hg, hn, hlt⟩
    have hnw := hg.scr.nowrap
    exact WP.mono (msRm1_ok hg hd.z hd.x (by have := hd.w4; omega) (by have := hd.w64; omega) (by rw [hn]; exact hlt))
      fun t ⟨_, ho, k⟩ => ⟨hk, k.2.2.trans hw, hd, mi, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
        Hdr.outside hg.hdr ho (by unfold slot; omega)⟩
  · exact kt_ct (fun q : TPub => q.B) (fun q => q.wr) gS (fun q => gvs q.B q.w) [] (by decide)
      (fun q => gvs_fst _ _) (fun _ _ h => h.hp) (pins_nil _) (by taint_decide)
  · rintro q s ⟨⟨hk, hw, hd, -⟩, hrl, mi, c, r, hg, hn, hsh, hO, hU, hR, hK, hRL, hUs, hsrc, hrlen, hrk, hS⟩
    obtain ⟨hodd, hlo, hhi⟩ := hsh
    have hw4 := hd.w4
    have hnw := hg.scr.nowrap
    have htop : 2 ^ (64 * q.w - 1) ≤ c := by
      have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
      omega
    refine WP.mono (montSetup_ok M hg hd.z hd.x hw4 hd.w64 hn hodd htop)
      fun t ⟨mi', hg', hinv, hr2, hr1, hrm1, hchk, hf, k⟩ => ?_
    have e : ∀ x, x = kOut ∨ x = kUsedP ∨ x = kRand ∨ x = kLen ∨ x = kRandLen ∨ x = kUsed →
        word t.mem q.B (8 * x) = word s.mem q.B (8 * x) := fun x hx => hf.word_eq (msRanges_hdr _ x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hx)) (by
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hn' : wv t.mem q.B (slot q.w aN) q.w = c := by
      rw [hf.wv_eq (d := slot q.w aN) (k := q.w) (by simp only [msRanges]; rng_disj)
        (by have := slot_le (w := q.w) (show aN < 8 by decide); have := hd.z; omega)]; exact hn
    have hle : ∀ r ∈ msRanges q.w, r.1 + r.2 ≤ q.Z := by
      have h1 := hd.x; simp only [slot, aRm1, hdrBytes] at h1; simp only [msRanges]; rng_le
    have hc1 : 1 < c := by have := Nat.two_pow_pos (64 * q.w - 2); omega
    have hch : Proof.RsaKeyGen.checksW q.w < 2 ^ 62 := by
      unfold Proof.RsaKeyGen.checksW; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> decide
    exact ⟨hk, ⟨hg'.rdi, k.2.2.trans hw, fun _ he => absurd he List.not_mem_nil⟩, hd.mr, hch, hrl, mi', c,
      wv t.mem q.B (slot q.w aB) q.w, r, ⟨hg', hinv, hn', rfl, hr1, hrm1⟩, hr2, hc1, ⟨hodd, hlo, hhi⟩,
      by rw [e _ (Or.inl rfl)]; exact hO, by rw [e _ (Or.inr (Or.inl rfl))]; exact hU,
      by rw [e _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hR, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hK,
      by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hRL, hrlen, hchk,
      hsrc.congrK (InScr.of_frm hf hle) k, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]; exact hUs,
      Nat.le_refl _, hrk, hS⟩

end VG.Proof.RsaKeyGen.X86_64
