module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsScan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, one height

`heightBody` (`height_ok`): the scan of the `c` nodes of height `z` into the
authentication path's node (`pick`), then the `c / 2` nodes of height
`z + 1` over the first of them.
-/

-- separate module: the whole function's proof (`LevelsMain`) changes without rebuilding the heights'.

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Tree
open VG.Proof.Sha3.X86_64 (Upd wp_addi wp_mov32i)

/-- `seq (seq a b) c` as `seq a (seq b c)`. -/
theorem wp_seq_seq {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun t => WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', he, t', s'', he', hq⟩ := h
  cases he with
  | seq h₁ h₂ => exact ⟨_, _, .seq h₁ (.seq h₂ he'), hq⟩

theorem getD_xorB {a b : List Byte} {j : Nat} (ha : j < a.length) (hb : j < b.length) :
    (xorB a b).getD j 0 = a.getD j 0 ^^^ b.getD j 0 := by
  simp [xorB, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem length_pick {n : Nat} {L : List (List Byte)} (hL : ∀ i < L.length, (L.getD i []).length = n)
    (first idx z : Nat) : (pick n L first idx z).length = n := by
  simp only [pick]
  by_cases h : first ≤ idx / 2 ^ z ^^^ 1 ∧ idx / 2 ^ z ^^^ 1 < first + L.length
  · rw [ite_eq_left h]; exact hL _ (by omega)
  · rw [ite_eq_right h]; exact length_toByte 0 n

/-- The scan's bytes are those of `pick`. -/
theorem scan_pick {m m' : Mem} {S AP : Addr} {no n first idx z c : Nat} {L : List (List Byte)}
    (hlen : L.length = c) (hL : ∀ i < c, bytesAt m (at' S (no + i * n)) n = L.getD i [])
    (h : ∀ j < n, m' (AP + BitVec.ofNat 64 j) =
      acc m S no n first (idx / 2 ^ z ^^^ 1) c j ^^^ m (AP + BitVec.ofNat 64 j)) :
    bytesAt m' AP n = xorB (bytesAt m AP n) (pick n L first idx z) := by
  have hl : ∀ i < L.length, (L.getD i []).length = n := fun i hi => by
    rw [← hL i (by omega)]; simp [bytesAt]
  refine bytesAt_eq (by simp [xorB, bytesAt, length_pick hl]) fun j hj => ?_
  rw [h j hj, getD_xorB (by simp [bytesAt]; omega) (by rw [length_pick hl]; exact hj), getD_bytesAt _ _ hj,
    BitVec.xor_comm]
  congr 1
  simp only [pick, acc]
  by_cases hc : first ≤ idx / 2 ^ z ^^^ 1 ∧ idx / 2 ^ z ^^^ 1 < first + c
  · rw [ite_eq_left hc, ite_eq_left (by rw [hlen]; exact hc), ← hL _ (by omega), getD_bytesAt _ _ hj, at_add]
  · rw [ite_eq_right hc, ite_eq_right (by rw [hlen]; exact hc), getD_toByte_zero]

variable {p : Params}

theorem scan_nm : (scanInit ++ scanBody ⟨p.n, p.len⟩).all (fun i => !loadsMxcsr i) = true := by
  simp only [scanInit, scanBody, List.all_append, List.all_flatMap, mulN_nm]
  simp [loadsMxcsr]

theorem shr_one (P : Nat) (hP : 2 * P < 2 ^ 64) : BitVec.ofNat 64 (2 * P) >>> 1 = BitVec.ofNat 64 P := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hP,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  omega

theorem sext_n (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) :
    (BitVec.ofNat 32 p.n).signExtend 64 = BitVec.ofNat 64 p.n := by
  rcases hn with h | h | h <;> rw [h] <;> decide

/-- A region outside `scratch` below `oSigTmp` and outside a part of it. -/
theorem disj_low {X : Region} {S : Addr} (h : X.Disjoint ⟨S, Layout.oSigTmp⟩) {o l : Nat}
    (ho : o + l ≤ Layout.oSigTmp) : X.Disjoint ⟨at' S o, l⟩ :=
  h.sub_right (Offset.sub_base S ho)

/-- What a height does. -/
structure HeightPost (p : Params) (S AP : Addr) (stack : Nat) (pkSeed a16 : List Byte) (t t' : State)
    (no z P ty kp x : Nat) (pk : List Byte) : Prop where
  keep : ∀ g ∈ [Reg.rbx, .r12, .rsp], t'.gpr g = t.gpr g
  r13 : t'.gpr .r13 = AP + BitVec.ofNat 64 p.n
  r14 : t'.gpr .r14 = BitVec.ofNat 64 (z + 1)
  r15 : t'.gpr .r15 = BitVec.ofNat 64 P
  zf : t'.zf = some (decide (P = 1))
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  mx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10
  env : Env p t'.mem S pkSeed a16
  node : ∀ q < P, bytesAt t'.mem (at' S (no + q * p.n)) p.n =
    H p pkSeed (nodeAdrs a16 ty kp (z + 1) (x + q)) (bytesAt t.mem (at' S (no + 2 * q * p.n)) (2 * p.n))
  auth : bytesAt t'.mem AP p.n = xorB (bytesAt t.mem AP p.n) pk
  vars : ∀ o, 2400 ≤ o → o + 8 ≤ 3296 → (o + 8 ≤ Layout.oVar 4 3 ∨ Layout.oVar 4 3 + 8 ≤ o) →
    t'.mem.readW (at' S o) 64 = t.mem.readW (at' S o) 64
  frame : Frame (lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, (P + 3) * p.n⟩, below (t.gpr .rsp) stack,
    ⟨AP, p.n⟩, ⟨at' S (Layout.oVar 4 3), 8⟩]) t.mem t'.mem

theorem height_ok (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S AP : Addr} {no z P : Nat} {V0 V5 V6 V7 V8 : BitVec 64} {pkSeed a16 : List Byte} {L : List (List Byte)}
    {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (h13 : t.gpr .r13 = AP)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 z) (h15 : t.gpr .r15 = BitVec.ofNat 64 (2 * P)) (hz : z < 14)
    (hP1 : 1 ≤ P) (hP : P ≤ 2 ^ 13) (hno : 12640 ≤ no) (hcap : no + (2 * P + 8) * p.n ≤ Layout.oSigTmp)
    (h0 : t.mem.readW (at' S (Layout.oVar 4 0)) 64 = V0) (h5 : t.mem.readW (at' S (Layout.oVar 4 5)) 64 = V5)
    (h6 : t.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6) (h7 : t.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7)
    (h8 : t.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8)
    (hV0 : V0.toNat < 2 ^ 32) (hV5 : V5.toNat < 2 ^ 32) (hV6 : V6.toNat < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hE : Env p t.mem S pkSeed a16)
    (ha : a16.length = 16)
    (hau : ∀ w < p.n / 8, InRegions t.wr (AP + BitVec.ofNat 64 (8 * w)) 8)
    (hAd : Region.Disjoint ⟨AP, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hAs : Region.Disjoint ⟨AP, p.n⟩ (below (t.gpr .rsp) stack))
    (hlen : L.length = 2 * P) (hL : ∀ i < 2 * P, bytesAt t.mem (at' S (no + i * p.n)) p.n = L.getD i []) :
    WP isa (heightBody ⟨p.n, p.len⟩ name T.code) t fun t' =>
      HeightPost p S AP stack pkSeed a16 t t' no z P V7.toNat V8.toNat (V6.toNat / 2 ^ (z + 1))
        (pick p.n L (V5.toNat / 2 ^ z) V0.toNat z) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eT : Layout.oSigTmp = 31648 := rfl
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  have hPn : (2 * P) * p.n + 8 * p.n ≤ (2 * P + 8) * p.n := by rw [Nat.add_mul]
  unfold heightBody
  refine wp_seq_seq (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using scan_nm)
    (scan_ok (Q := fun u => u.mxcsr = t.mxcsr → _) hn hbx h12 h13 h14 h15 (by omega) (by omega) (by omega) hw
      (by omega) (by omega_using [hcap, hPn]) h0 h5 hV0 hV5 hau hAd fun t₁ g₁ rd₁ wr₁ by₁ f₁ mx₁ => ?_)
    fun _ hq hmx => hq hmx)
  -- after the scan
  have hk₁ : ∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], t₁.gpr g = t.gpr g := fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hd3 : ∀ o l, o + l ≤ Layout.oSigTmp → (o + l ≤ Layout.oVar 4 3 ∨ Layout.oVar 4 3 + 8 ≤ o) →
      ∀ r ∈ [(⟨AP, p.n⟩ : Region), ⟨at' S (Layout.oVar 4 3), 8⟩], Region.Disjoint ⟨at' S o, l⟩ r := fun o l h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (disj_low hAd h₁).symm
    · exact disj_scr S h₂ (by omega) (by rw [hv]; omega)
  have hrd₁ : ∀ o, 2400 ≤ o → o + 8 ≤ 3296 → (o + 8 ≤ Layout.oVar 4 3 ∨ Layout.oVar 4 3 + 8 ≤ o) →
      t₁.mem.readW (at' S o) 64 = t.mem.readW (at' S o) 64 := fun o h₁ h₂ h₃ =>
    f₁.readW (r := ⟨at' S o, 8⟩) (Region.contains_self _ _) (hd3 o 8 (by omega) h₃) (by decide)
  have hE₁ : Env p t₁.mem S pkSeed a16 := by
    have hb : ∀ o l, o + l ≤ 10480 → 3296 ≤ o → bytesAt t₁.mem (at' S o) l = bytesAt t.mem (at' S o) l :=
      fun o l h₁ h₂ => bytesAt_congr fun i hi =>
        f₁.bytes (R := ⟨at' S o, l⟩) (hd3 o l (by omega) (.inr (by rw [hv]; omega))) (show l ≤ 2 ^ 64 by omega) hi
    have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
    have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
    refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hE.rc r hr k hk]
      exact f₁.readW (r := ⟨at' S (1600 + 32 * r + 8 * k), 8⟩) (Region.contains_self _ _)
        (hd3 _ 8 (by omega) (.inl (by rw [hv]; omega))) (by decide)
    · rw [← hE.seedA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE.seedB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
    · rw [← hE.adrsA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE.adrsB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
  -- `halve`
  refine WP.seq (WP.mono_mx (by rfl) (Q := fun u => (∀ g, g ≠ .r15 → g ≠ .rbp → u.gpr g = t₁.gpr g) ∧
      u.gpr .r15 = BitVec.ofNat 64 P ∧ u.gpr .rbp = BitVec.ofNat 64 0 ∧ u.mem = t₁.mem ∧ u.rd = t₁.rd ∧ u.wr = t₁.wr)
    (wp_shr (d := .r15) (by decide) (by decide) fun u₁ v₁ => wp_mov32i (d := .rbp) fun u₂ v₂ =>
      WP.block_nil ⟨fun g h₁ h₂ => by rw [v₂.other _ h₂, v₁.other _ h₁],
        by rw [v₂.other _ (by decide), v₁.gpr, hk₁ .r15 (by simp), h15, shr_one P (by omega)],
        by rw [v₂.gpr]; rfl, by rw [v₂.mem, v₁.mem], by rw [v₂.rd, v₁.rd], by rw [v₂.wr, v₁.wr]⟩)
    fun u₂ hu mx₂ => ?_)
  obtain ⟨g₂, r15₂, bp₂, m₂, rd₂, wr₂⟩ := hu
  have hk₂ : ∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .rsp], u₂.gpr g = t.gpr g := fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide) (by decide), hk₁ _ (by simp)]
  have hvar : ∀ i, i ≠ 3 → i < 42 → u₂.mem.readW (at' S (Layout.oVar 4 i)) 64 = t.mem.readW (at' S (Layout.oVar 4 i)) 64 :=
    fun i h₁ h₂ => by
      rw [m₂, hrd₁ _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv, hv]; omega)]
  have hcap' : no + (2 * P + 8) * p.n ≤ 2 ^ 16 := by omega
  refine WP.seq (WP.mono (level_ok T name hn hf hst hs63 (P := P) (V6 := V6) (V7 := V7) (V8 := V8)
    (by rw [hk₂ .rbx (by simp), hbx]) (by rw [hk₂ .r12 (by simp), h12]) (by rw [hk₂ .r14 (by simp), h14]) bp₂ r15₂
    hz hP1 hP hno hcap' (by rw [hvar 6 (by decide) (by decide), h6]) (by rw [hvar 7 (by decide) (by decide), h7])
    (by rw [hvar 8 (by decide) (by decide), h8]) hV6 (by rw [wr₂, wr₁]; exact hw) hS
    (by rw [hk₂ .rsp (by simp)]; exact hstk) (by rw [m₂]; exact hE₁) ha) fun v lp => ?_)
  -- `nextHeight`
  refine WP.mono_mx (by rfl) (Q := fun w => w.gpr .rbx = v.gpr .rbx ∧ w.gpr .r12 = v.gpr .r12 ∧ w.gpr .rsp = v.gpr .rsp ∧
      w.gpr .r13 = v.gpr .r13 + BitVec.ofNat 64 p.n ∧ w.gpr .r14 = v.gpr .r14 + 1 ∧ w.gpr .r15 = v.gpr .r15 ∧
      w.zf = some (v.gpr .r15 - 1 == 0) ∧ w.mem = v.mem ∧ w.rd = v.rd ∧ w.wr = v.wr)
    (wp_addi fun w₁ x₁ => wp_addi fun w₂ x₂ => wp_cmpi fun w₃ g₃ m₃ r₃ wr₃ z₃ => WP.block_nil
      ⟨by rw [g₃, x₂.other _ (by decide), x₁.other _ (by decide)], by rw [g₃, x₂.other _ (by decide), x₁.other _ (by decide)],
        by rw [g₃, x₂.other _ (by decide), x₁.other _ (by decide)],
        by rw [g₃, x₂.other _ (by decide), x₁.gpr, sext_n hn],
        by rw [g₃, x₂.gpr, x₁.other _ (by decide)]; rfl,
        by rw [g₃, x₂.other _ (by decide), x₁.other _ (by decide)],
        by rw [z₃, x₂.other _ (by decide), x₁.other _ (by decide)]; rfl,
        by rw [m₃, x₂.mem, x₁.mem], by rw [r₃, x₂.rd, x₁.rd], by rw [wr₃, x₂.wr, x₁.wr]⟩)
    fun w ⟨bx₃, r12₃, sp₃, r13₃, r14₃, r15₃, zf₃, m₃, rd₃, wr₃⟩ mx₃ => ?_
  have lfr := lp.frame
  rw [hk₂ .rsp (by simp)] at lfr
  have hkv : ∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], v.gpr g = u₂.gpr g := lp.keep
  have r15v : v.gpr .r15 = BitVec.ofNat 64 P := by rw [hkv .r15 (by simp), r15₂]
  -- what the level loop keeps: outside `scratch` below `oSigTmp` but its parts, and the stack
  have hlvl : ∀ X : Region, X.Disjoint ⟨S, Layout.oSigTmp⟩ → X.Disjoint (below (t.gpr .rsp) stack) →
      ∀ r ∈ lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, (P + 3) * p.n⟩, below (t.gpr .rsp) stack],
        X.Disjoint r := fun X h₁ h₂ r hr => by
    have hP3 : (P + 3) * p.n ≤ (2 * P + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
    rcases List.mem_append.mp hr with hr | hr
    · simp only [lanesR, List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      have := laneA_le k hk
      exact disj_low h₁ (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · have hs : Region.Sub ⟨S + BitVec.ofNat 64 0, 1600⟩ ⟨S, Layout.oSigTmp⟩ := Offset.sub_base S (by omega)
        rw [← scr0 S] at hs
        exact h₁.sub_right hs
      · exact disj_low h₁ (by omega)
      · exact disj_low h₁ (by omega)
      · exact h₂
  have hbA : bytesAt w.mem AP p.n = bytesAt t₁.mem AP p.n := by
    rw [m₃, ← m₂]
    exact bytesAt_congr fun i hi => by
      have e := lfr.bytes (R := ⟨AP, p.n⟩) (hlvl _ hAd hAs) (show p.n ≤ 2 ^ 64 by omega) hi
      simpa using e
  refine ⟨fun g hg => ?_, ?_, ?_, ?_, ?_, by rw [rd₃, lp.rd, rd₂, rd₁], by rw [wr₃, lp.wr, wr₂, wr₁],
    by rw [mx₃, lp.mx, mx₂, mx₁], by rw [m₃]; exact lp.env, fun q hq => ?_, ?_, fun o h₁ h₂ h₃ => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · rw [bx₃, hkv _ (by simp), hk₂ _ (by simp)]
    · rw [r12₃, hkv _ (by simp), hk₂ _ (by simp)]
    · rw [sp₃, hkv _ (by simp), hk₂ _ (by simp)]
  · rw [r13₃, hkv _ (by simp), hk₂ _ (by simp), h13]
  · rw [r14₃, hkv _ (by simp), hk₂ _ (by simp), h14, BitVec.ofNat_add]; rfl
  · rw [r15₃, r15v]
  · rw [zf₃, r15v]
    congr 1
    by_cases h1 : P = 1
    · subst h1; decide
    · have : BitVec.ofNat 64 P - 1 ≠ 0#64 := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := P) (by omega),
          show (1 : BitVec 64).toNat = 1 from rfl, show (0#64).toNat = 0 from rfl] at this
        omega
      simpa [h1] using this
  · have hq2 : (2 * q + 2) * p.n ≤ (2 * P) * p.n := Nat.mul_le_mul_right _ (by omega)
    rw [m₃, lp.node q hq, m₂]
    congr 1
    refine bytesAt_congr fun i hi => f₁.bytes (R := ⟨at' S (no + 2 * q * p.n), 2 * p.n⟩)
      (hd3 _ _ (by grind) (.inr (by rw [hv]; omega))) (show 2 * p.n ≤ 2 ^ 64 by omega) hi
  · rw [hbA]; exact scan_pick hlen hL by₁
  · rw [m₃, keep_low hn32 lfr (by omega) (by grind) hstk h₁ h₂, m₂, hrd₁ o h₁ h₂ h₃]
  · have f₂ : Frame (lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, (P + 3) * p.n⟩, below (t.gpr .rsp) stack])
        t₁.mem w.mem := by rw [m₃, ← m₂]; exact lfr
    refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
    · rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · refine List.mem_append_right _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl <;> simp

/-! ## The heights -/

theorem bytesAt_two (m : Mem) (S : Addr) (o n : Nat) :
    bytesAt m (at' S o) (2 * n) = bytesAt m (at' S o) n ++ bytesAt m (at' S (o + n)) n := by
  simp only [bytesAt, Nat.two_mul, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, at_add, Nat.add_assoc]

theorem getD_nodesAt (m : Mem) (a : Addr) {c i : Nat} (hi : i < c) :
    (nodesAt p m a c).getD i [] = bytesAt m (a + BitVec.ofNat 64 (i * p.n)) p.n := by
  simp [nodesAt, List.getD_eq_getElem?_getD, hi]

theorem length_nodesAt (m : Mem) (a : Addr) (c : Nat) : (nodesAt p m a c).length = c := by
  simp [nodesAt]

/-- Every region of `changes` is in `scratch` below `oSigTmp`. -/
theorem changes_low (hn32 : p.n ≤ 32) (S : Addr) : ∀ r ∈ changes p S, Region.Sub r ⟨S, Layout.oSigTmp⟩ := by
  have eT : Layout.oSigTmp = 31648 := rfl
  intro r hr
  simp only [changes, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with ((h | h | h) | ⟨k, hk, h | h⟩) | (h | h | h | h | h) <;> subst h
  · have hs : Region.Sub ⟨S + BitVec.ofNat 64 0, 1600⟩ ⟨S, Layout.oSigTmp⟩ := Offset.sub_base S (by omega)
    rw [← scr0 S] at hs; exact hs
  · exact Offset.sub_base S (by omega)
  · exact Offset.sub_base S (by rw [show Layout.oVars = 2400 from rfl]; omega)
  · exact Offset.sub_base S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact Offset.sub_base S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oDigits = 30368 from rfl]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oRoots = 29280 from rfl]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oMsg = 30496 from rfl]; omega)
  · exact Offset.sub_base S (by rw [show Layout.oFidx = 31328 from rfl]; omega)

/-- Every region of `levelsChanges` is in `scratch` below `oSigTmp`. -/
theorem levelsChanges_low (hn32 : p.n ≤ 32) (S : Addr) {no c : Nat} (hc : no + (c + 8) * p.n ≤ Layout.oSigTmp) :
    ∀ r ∈ levelsChanges p S (at' S no) c, Region.Sub r ⟨S, Layout.oSigTmp⟩ := by
  have eT : Layout.oSigTmp = 31648 := rfl
  intro r hr
  simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with ⟨k, hk, rfl⟩ | (rfl | rfl | rfl | rfl)
  · exact Offset.sub_base S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · have hs : Region.Sub ⟨S + BitVec.ofNat 64 0, 1600⟩ ⟨S, Layout.oSigTmp⟩ := Offset.sub_base S (by omega)
    rw [← scr0 S] at hs; exact hs
  · exact Offset.sub_base S (by omega)
  · exact Offset.sub_base S (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega)
  · exact Offset.sub_base S (by omega)

/-- The regions a height changes are in those of `levels`. -/
theorem height_sub {S AU : Addr} {sp : Addr} {stack no l r c : Nat} (hl : l ≤ (c + 8) * p.n) :
    ∀ x ∈ lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, l⟩, below sp stack,
      ⟨AU + BitVec.ofNat 64 (r * p.n), p.n⟩, ⟨at' S (Layout.oVar 4 3), 8⟩],
      ∃ y ∈ levelsChanges p S (at' S no) c ++ [⟨AU, (r + 1) * p.n⟩, below sp stack], Region.Sub x y := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [levelsChanges], fun _ h => h⟩
    · exact ⟨_, by simp [levelsChanges], fun _ h => h⟩
    · exact ⟨_, by simp [levelsChanges], Region.sub_prefix hl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨AU, (r + 1) * p.n⟩, by simp, Offset.sub_base AU (by rw [Nat.add_mul, Nat.one_mul])⟩
    · exact ⟨⟨at' S (Layout.oFrame 4), 128⟩, by simp [levelsChanges], Offset.sub S (by decide) (by decide)⟩

/-- What the heights do, from `t` (after the prologue). -/
structure HeightsPost (p : Params) (S AU : Addr) (stack : Nat) (pkSeed a16 : List Byte) (t t' : State)
    (no h z₀ ty kp base first idx : Nat) (L : List (List Byte)) : Prop where
  bx : t'.gpr .rbx = t.gpr .rbx
  sp : t'.gpr .rsp = t.gpr .rsp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  mx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10
  env : Env p t'.mem S pkSeed a16
  root : bytesAt t'.mem (at' S no) p.n = (upNodes p pkSeed a16 ty kp base z₀ L h).getD 0 []
  auth : ∀ r < h, bytesAt t'.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n =
    xorB (bytesAt t.mem (AU + BitVec.ofNat 64 (r * p.n)) p.n)
      (pick p.n (upNodes p pkSeed a16 ty kp base z₀ L r) (first / 2 ^ (z₀ + r)) idx (z₀ + r))
  vars : ∀ o, 2400 ≤ o → o + 8 ≤ Layout.oVar 4 3 → t'.mem.readW (at' S o) 64 = t.mem.readW (at' S o) 64
  frame : Frame (levelsChanges p S (at' S no) (2 ^ h) ++ [⟨AU, h * p.n⟩, below (t.gpr .rsp) stack]) t.mem t'.mem

theorem heights_ok (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S AU : Addr} {no h z₀ : Nat} {V0 V5 V6 V7 V8 : BitVec 64} {pkSeed a16 : List Byte} {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (h13 : t.gpr .r13 = AU)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 z₀) (h15 : t.gpr .r15 = BitVec.ofNat 64 (2 ^ h)) (hh : 1 ≤ h)
    (hzh : z₀ + h ≤ 14) (hno : 12640 ≤ no) (hcap : no + (2 ^ h + 8) * p.n ≤ Layout.oSigTmp)
    (hnoR : ∀ l ≤ (2 ^ h + 3) * p.n, Region.Sub ⟨at' S no, l⟩ ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩ ∨
      Region.Sub ⟨at' S no, l⟩ ⟨at' S Layout.oRoots, 1024⟩)
    (h0 : t.mem.readW (at' S (Layout.oVar 4 0)) 64 = V0) (h5 : t.mem.readW (at' S (Layout.oVar 4 5)) 64 = V5)
    (h6 : t.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6) (h7 : t.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7)
    (h8 : t.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8)
    (hV0 : V0.toNat < 2 ^ 32) (hV5 : V5.toNat < 2 ^ 32) (hV6 : V6.toNat < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hE : Env p t.mem S pkSeed a16)
    (ha : a16.length = 16)
    (hAw : (⟨AU, h * p.n⟩ : Region) ∈ t.wr) (hAf : AU.toNat + h * p.n ≤ 2 ^ 64)
    (hAd : Region.Disjoint ⟨AU, h * p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hAs : Region.Disjoint ⟨AU, h * p.n⟩ (below (t.gpr .rsp) stack)) :
    WP isa (.loop (heightBody ⟨p.n, p.len⟩ name T.code) .ne) t fun t' =>
      HeightsPost p S AU stack pkSeed a16 t t' no h z₀ V7.toNat V8.toNat V6.toNat V5.toNat V0.toNat
        (nodesAt p t.mem (at' S no) (2 ^ h)) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have h2h : 2 ^ h ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) (by omega)
  -- the parts of `auth`
  have hAr : ∀ r < h, (r + 1) * p.n ≤ h * p.n := fun r hr => Nat.mul_le_mul_right _ (by omega)
  have hAsub : ∀ r < h, Region.Sub ⟨AU + BitVec.ofNat 64 (r * p.n), p.n⟩ ⟨AU, h * p.n⟩ := fun r hr =>
    Offset.sub_base AU (by have := hAr r hr; rw [Nat.add_mul, Nat.one_mul] at this; exact this)
  -- the invariant at height `z₀ + r`
  let L₀ := nodesAt p t.mem (at' S no) (2 ^ h)
  let Inv : Nat → State → Prop := fun m s => ∃ r, m = h - r ∧ r < h ∧
    s.gpr .rbx = S ∧ s.gpr .r12 = at' S no ∧ s.gpr .r13 = AU + BitVec.ofNat 64 (r * p.n) ∧
    s.gpr .r14 = BitVec.ofNat 64 (z₀ + r) ∧ s.gpr .r15 = BitVec.ofNat 64 (2 ^ (h - r)) ∧
    s.gpr .rsp = t.gpr .rsp ∧ s.rd = t.rd ∧ s.wr = t.wr ∧
    s.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧ Env p s.mem S pkSeed a16 ∧
    (∀ o, 2400 ≤ o → o + 8 ≤ 3296 → (o + 8 ≤ Layout.oVar 4 3 ∨ Layout.oVar 4 3 + 8 ≤ o) →
      s.mem.readW (at' S o) 64 = t.mem.readW (at' S o) 64) ∧
    (∀ i < 2 ^ (h - r), bytesAt s.mem (at' S (no + i * p.n)) p.n =
      (upNodes p pkSeed a16 V7.toNat V8.toNat V6.toNat z₀ L₀ r).getD i []) ∧
    (∀ r' < r, bytesAt s.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n =
      xorB (bytesAt t.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n)
        (pick p.n (upNodes p pkSeed a16 V7.toNat V8.toNat V6.toNat z₀ L₀ r') (V5.toNat / 2 ^ (z₀ + r')) V0.toNat
          (z₀ + r'))) ∧
    Frame (levelsChanges p S (at' S no) (2 ^ h) ++ [⟨AU, r * p.n⟩, below (t.gpr .rsp) stack]) t.mem s.mem
  refine WP.loop (M := isa) Inv (fun m s hI => ?_) h t ⟨0, by omega, hh, hbx, h12, by rw [h13]; simp, by simpa using h14,
    by simpa using h15, rfl, rfl, rfl, rfl, hE, fun _ _ _ _ => rfl, fun i hi => ?_, fun _ h => absurd h (by omega),
    Frame.refl _ _⟩
  rotate_left
  · simp only [upNodes]
    rw [getD_nodesAt _ _ (by simpa using hi), at_add]
  obtain ⟨r, rfl, hr, hbx', h12', h13', h14', h15', hsp', hrd', hwr', hmx', hE', hvar', hnode', hauth', hfr'⟩ := hI
  -- the numbers of nodes
  obtain ⟨P, hP2⟩ : ∃ P, 2 ^ (h - r) = 2 * P := by
    obtain ⟨k, hk⟩ : ∃ k, h - r = k + 1 := ⟨h - r - 1, by omega⟩
    exact ⟨2 ^ k, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
  have hPh : 2 * P ≤ 2 ^ h := by rw [← hP2]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hP1 : 1 ≤ P := by have : 1 ≤ 2 ^ (h - r) := Nat.one_le_two_pow; omega
  have hPc : (2 * P + 8) * p.n ≤ (2 ^ h + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hP3 : (P + 3) * p.n ≤ (2 ^ h + 3) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hlen : (upNodes p pkSeed a16 V7.toNat V8.toNat V6.toNat z₀ L₀ r).length = 2 * P := by
    rw [length_upNodes, length_nodesAt, Nat.pow_div (by omega) (by decide), hP2]
  have hrv : ∀ i, i ≠ 3 → i < 42 → s.mem.readW (at' S (Layout.oVar 4 i)) 64 = t.mem.readW (at' S (Layout.oVar 4 i)) 64 :=
    fun i h₁ h₂ => hvar' _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv, hv]; omega)
  have hAr' : r * p.n + p.n ≤ h * p.n := by have := hAr r hr; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  refine WP.mono (height_ok T name hn hf hst hs63 (P := P) (V0 := V0) (V5 := V5) (V6 := V6) (V7 := V7) (V8 := V8)
    (L := upNodes p pkSeed a16 V7.toNat V8.toNat V6.toNat z₀ L₀ r) hbx' h12' h13' h14' (by rw [h15', hP2])
    (by omega) hP1 (by omega) hno (by omega) (by rw [hrv 0 (by decide) (by decide), h0])
    (by rw [hrv 5 (by decide) (by decide), h5]) (by rw [hrv 6 (by decide) (by decide), h6])
    (by rw [hrv 7 (by decide) (by decide), h7]) (by rw [hrv 8 (by decide) (by decide), h8]) hV0 hV5 hV6
    (by rw [hwr']; exact hw) hS (by rw [hsp']; exact hstk) hE' ha (fun w hw' => ?_)
    (hAd.sub_left (hAsub r hr)) (by rw [hsp']; exact hAs.sub_left (hAsub r hr)) hlen
    (fun i hi => hnode' i (by omega))) fun s' hp => ?_
  · refine ⟨_, by rw [hwr']; exact hAw, ?_⟩
    rw [add_add]
    have : 8 * w + 8 ≤ p.n := by omega
    exact Offset.contains_base AU (by omega) (by omega)
  -- after the height
  have hPd : P = 2 ^ (h - (r + 1)) := by
    obtain ⟨k, hk⟩ : ∃ k, h - r = k + 1 := ⟨h - r - 1, by omega⟩
    rw [show h - (r + 1) = k by omega]
    rw [hk, Nat.pow_succ] at hP2
    omega
  have hPc' : (P + 3) * p.n ≤ (2 ^ h + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hsp₂ : s'.gpr .rsp = t.gpr .rsp := by rw [hp.keep _ (by simp), hsp']
  have hfr₂ := hp.frame
  rw [hsp'] at hfr₂
  have hnodes : ∀ q < P, bytesAt s'.mem (at' S (no + q * p.n)) p.n =
      (upNodes p pkSeed a16 V7.toNat V8.toNat V6.toNat z₀ L₀ (r + 1)).getD q [] := fun q hq => by
    rw [hp.node q hq, upNodes_succ, getD_step _ _ _ _ _ _ _ _ (by rw [hlen]; omega), bytesAt_two, hnode' (2 * q) (by omega),
      show no + 2 * q * p.n + p.n = no + (2 * q + 1) * p.n by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc],
      hnode' (2 * q + 1) (by omega)]
  -- `auth` outside what the height changes, but its node
  have hout : ∀ r' < h, r' ≠ r → bytesAt s'.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n =
      bytesAt s.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n := fun r' hr' hne => by
    have hX := hAsub r' hr'
    have hr2 : r' * p.n + p.n ≤ h * p.n := by have := hAr r' hr'; rw [Nat.add_mul, Nat.one_mul] at this; exact this
    refine bytesAt_congr fun i hi => hfr₂.bytes (R := ⟨AU + BitVec.ofNat 64 (r' * p.n), p.n⟩) (fun x hx => ?_)
      (show p.n ≤ 2 ^ 64 by omega) hi
    rcases List.mem_append.mp hx with hx | hx
    · simp only [lanesR, List.mem_map, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have := laneA_le k hk
      exact disj_low (hAd.sub_left hX) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · have hs : Region.Sub ⟨S + BitVec.ofNat 64 0, 1600⟩ ⟨S, Layout.oSigTmp⟩ := Offset.sub_base S (by omega)
        rw [← scr0 S] at hs
        exact (hAd.sub_left hX).sub_right hs
      · exact disj_low (hAd.sub_left hX) (by omega)
      · exact disj_low (hAd.sub_left hX) (by omega)
      · exact hAs.sub_left hX
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have : (r' + 1) * p.n ≤ r * p.n := Nat.mul_le_mul_right _ hlt
          exact Offset.disjoint AU (.inl (by rw [Nat.add_mul, Nat.one_mul] at this; exact this)) (by omega) (by omega)
        · have : (r + 1) * p.n ≤ r' * p.n := Nat.mul_le_mul_right _ hlt
          exact Offset.disjoint AU (.inr (by rw [Nat.add_mul, Nat.one_mul] at this; exact this)) (by omega) (by omega)
      · exact disj_low (hAd.sub_left hX) (by rw [hv]; omega)
  have hauth : ∀ r' < r + 1, bytesAt s'.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n =
      xorB (bytesAt t.mem (AU + BitVec.ofNat 64 (r' * p.n)) p.n)
        (pick p.n (upNodes p pkSeed a16 V7.toNat V8.toNat V6.toNat z₀ L₀ r') (V5.toNat / 2 ^ (z₀ + r')) V0.toNat
          (z₀ + r')) := fun r' hr' => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr' with hlt | rfl
    · rw [hout r' (by omega) (by omega), hauth' r' hlt]
    · rw [hp.auth]
      congr 1
      refine bytesAt_congr fun i hi => hfr'.bytes (R := ⟨AU + BitVec.ofNat 64 (r' * p.n), p.n⟩) (fun x hx => ?_)
        (show p.n ≤ 2 ^ 64 by omega) hi
      rcases List.mem_append.mp hx with hx | hx
      · exact (hAd.sub_left (hAsub r' hr)).sub_right (levelsChanges_low hn32 S hcap x hx)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact Offset.disjoint_base AU (Nat.le_refl _) (by omega)
        · exact hAs.sub_left (hAsub r' hr)
  have hfr₃ : Frame (levelsChanges p S (at' S no) (2 ^ h) ++ [⟨AU, (r + 1) * p.n⟩, below (t.gpr .rsp) stack])
      t.mem s'.mem := by
    refine (hfr'.sub fun x hx => ?_).trans (hfr₂.sub (height_sub (by omega)))
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, List.mem_append_left _ hx, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · have hs : Region.Sub ⟨AU + BitVec.ofNat 64 0, r * p.n⟩ ⟨AU, (r + 1) * p.n⟩ :=
          Offset.sub_base AU (by rw [Nat.add_mul, Nat.one_mul]; omega)
        rw [← scr0 AU] at hs
        exact ⟨⟨AU, (r + 1) * p.n⟩, by simp, hs⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have hvars : ∀ o, 2400 ≤ o → o + 8 ≤ 3296 → (o + 8 ≤ Layout.oVar 4 3 ∨ Layout.oVar 4 3 + 8 ≤ o) →
      s'.mem.readW (at' S o) 64 = t.mem.readW (at' S o) 64 := fun o h₁ h₂ h₃ => by
    rw [hp.vars o h₁ h₂ h₃, hvar' o h₁ h₂ h₃]
  by_cases hend : r + 1 = h
  · have hP1' : P = 1 := by rw [hPd, ← hend, Nat.sub_self, Nat.pow_zero]
    refine .inl ⟨by show s'.zf.map (!·) = _; rw [hp.zf]; simp [hP1'], ?_⟩
    subst hend
    refine ⟨by rw [hp.keep _ (by simp), hbx', hbx], hsp₂, by rw [hp.rd, hrd'], by rw [hp.wr, hwr'],
      by rw [hp.mx, hmx'], hp.env, ?_, hauth, fun o h₁ h₂ => hvars o h₁ (by rw [hv] at h₂; omega) (.inl h₂), hfr₃⟩
    have := hnodes 0 (by omega)
    simpa using this
  · have hP1' : P ≠ 1 := by
      intro h1
      rw [hPd] at h1
      have : h - (r + 1) = 0 := by
        rcases Nat.eq_zero_or_pos (h - (r + 1)) with h0 | h0
        · exact h0
        · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h0; simp at this; omega
      omega
    refine .inr ⟨by show s'.zf.map (!·) = _; rw [hp.zf]; simp [hP1'], h - (r + 1), by omega, r + 1, rfl, by omega,
      by rw [hp.keep _ (by simp), hbx'], by rw [hp.keep _ (by simp), h12'],
      by rw [hp.r13, add_add, Nat.add_mul, Nat.one_mul], by rw [hp.r14, Nat.add_assoc],
      by rw [hp.r15, hPd], hsp₂, by rw [hp.rd, hrd'], by rw [hp.wr, hwr'], by rw [hp.mx, hmx'], hp.env, hvars,
      fun i hi => hnodes i (by omega), hauth, hfr₃⟩

end VG.Proof.SlhDsa.X86_64.Levels
