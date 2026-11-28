module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsLevel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, one group of four nodes

`levelBody`: the lanes of the nodes `j` to `j + 3` of height `z + 1`, four
`H`s, and their outputs to the nodes (`group_ok`): node `j + k` is
`H(PK.seed, nodeAdrs …, node 2(j+k) ‖ node 2(j+k)+1)`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Tree

/-- What a group does. -/
structure GroupPost (p : Params) (S : Addr) (stack : Nat) (pkSeed a16 : List Byte) (t t' : State)
    (no z j P ty kp x : Nat) : Prop where
  keep : ∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], t'.gpr g = t.gpr g
  bp : t'.gpr .rbp = BitVec.ofNat 64 (j + 4)
  cf : t'.cf = some (decide (j + 4 < P))
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  mx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10
  env : Env p t'.mem S pkSeed a16
  node : ∀ k < 4, bytesAt t'.mem (at' S (no + (j + k) * p.n)) p.n =
    H p pkSeed (nodeAdrs a16 ty kp (z + 1) (x + k)) (bytesAt t.mem (at' S (no + 2 * (j + k) * p.n)) (2 * p.n))
  frame : Frame ((List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
    [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (no + j * p.n), 4 * p.n⟩, below (t.gpr .rsp) stack]) t.mem t'.mem

/-- Two frames over lists of regions, one after the other. -/
theorem frame_trans3 {r₁ r₂ r₃ R : List Region} {a b c d : Mem} (f₁ : Frame r₁ a b) (f₂ : Frame r₂ b c)
    (f₃ : Frame r₃ c d) (h₁ : ∀ r ∈ r₁, r ∈ R) (h₂ : ∀ r ∈ r₂, r ∈ R) (h₃ : ∀ r ∈ r₃, r ∈ R) : Frame R a d :=
  ((f₁.mono h₁).trans (f₂.mono h₂)).trans (f₃.mono h₃)

theorem at_add (S : Addr) (a i : Nat) : at' S a + BitVec.ofNat 64 i = at' S (a + i) := by
  rw [at', at', BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem twice_mul (no j k n : Nat) : no + 2 * j * n + 2 * n * k = no + 2 * (j + k) * n := by grind

variable {p : Params}

theorem mulN_nm (n : Nat) (r t : Reg) :
    (Impl.SlhDsa.X86_64.Wots.mulN n r t).all (fun i => !loadsMxcsr i) = true := by
  unfold Impl.SlhDsa.X86_64.Wots.mulN; split <;> rfl

theorem copyWords_nm (t : Reg) (d₂ : Nat) (s : Reg) (d₁ w : Nat) :
    (_root_.VG.Impl.SlhDsa.X86_64.copyWords t d₂ s d₁ w).all (fun i => !loadsMxcsr i) = true := by
  simp [_root_.VG.Impl.SlhDsa.X86_64.copyWords, List.all_flatMap, loadsMxcsr]

theorem lanes_nm : (levelLanes ⟨p.n, p.len⟩).all (fun i => !loadsMxcsr i) = true := by
  simp only [levelLanes, nodeLane, List.all_append, List.all_flatMap, mulN_nm,
    copyWords_nm, _root_.VG.Impl.SlhDsa.X86_64.setFieldR]
  simp [loadsMxcsr]

theorem out_nm : (levelOut ⟨p.n, p.len⟩).all (fun i => !loadsMxcsr i) = true := by
  simp only [levelOut, List.all_append, List.all_flatMap, mulN_nm, copyWords_nm]
  simp [loadsMxcsr]

theorem group_ok (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no z j P : Nat} {V6 V7 V8 : BitVec 64} {pkSeed a16 : List Byte} {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (h14 : t.gpr .r14 = BitVec.ofNat 64 z)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 j) (h15 : t.gpr .r15 = BitVec.ofNat 64 P) (hz : z < 14) (hj : j < 2 ^ 14)
    (hP : P < 2 ^ 64) (hno : 12640 ≤ no) (hno' : no + 2 * j * p.n + 8 * p.n ≤ 2 ^ 16)
    (h6 : t.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6) (h7 : t.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7)
    (h8 : t.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8) (hV6 : V6.toNat < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hE : Env p t.mem S pkSeed a16)
    (ha : a16.length = 16) :
    WP isa (levelBody ⟨p.n, p.len⟩ name T.code) t fun t' =>
      GroupPost p S stack pkSeed a16 t t' no z j P V7.toNat V8.toNat (V6.toNat / 2 ^ (z + 1) + j) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have hjn : no + j * p.n + 4 * p.n ≤ 2 ^ 16 := by have h := hno'; rw [Nat.mul_assoc] at h; omega
  unfold levelBody
  refine WP.seq (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using lanes_nm) (lanes_ok hn hbx h12 h14 hbp hz hj (by omega) hno' h6 h7 h8 hV6 hw)
    fun t₁ l mx₁ => ?_)
  -- the lanes changed only their fields and messages
  have lf₁ := l.frame
  have hrc₁ : RcTable t₁.mem S := fun r hr k hk => by
    rw [← hE.rc r hr k hk]
    refine lf₁.readW (r := ⟨at' S (1600 + 32 * r + 8 * k), 8⟩) (Region.contains_self _ _) (fun R hR => ?_) (by decide)
    simp only [List.mem_map, List.mem_range] at hR
    obtain ⟨k', hk', rfl⟩ := hR
    exact disj_scr S (.inl (by rw [hLA]; omega_using [hr, hk])) (by omega_using [hr, hk])
      (by rw [hLA]; omega_using [hk', hn32])
  have hbx₁ : t₁.gpr .rbx = S := by rw [l.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), hbx]
  have hsp₁ : t₁.gpr .rsp = t.gpr .rsp := l.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  refine WP.seq (WP.mono (t4_ok T name hn hst hs63 hbx₁ (by rw [l.wr]; exact hw) hS (by rw [hsp₁]; exact hstk) hrc₁)
    fun t₂ ⟨rd₂, wr₂, cs₂, mx₂, out₂, f₂⟩ => ?_)
  have g₂ : ∀ g ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], t₂.gpr g = t₁.gpr g := fun g hg =>
    cs₂ g (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hbx₂ : t₂.gpr .rbx = S := by rw [g₂ .rbx (by simp), hbx₁]
  have k₁ : ∀ g ∈ [Reg.r12, .r13, .r14, .r15, .rbp], t₁.gpr g = t.gpr g := fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact l.gpr _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  refine WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using out_nm) (out_ok hn hbx₂ (by rw [g₂ .r12 (by simp), k₁ .r12 (by simp), h12])
    (by rw [g₂ .rbp (by simp), k₁ .rbp (by simp), hbp]) (by rw [g₂ .r15 (by simp), k₁ .r15 (by simp), h15])
    (by omega_using [hj]) hP (by omega) (by grind) (by rw [wr₂, l.wr]; exact hw)) fun t₃ o mx₃ => ?_
  -- the frames
  have hR : ∀ r ∈ (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
      [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (no + j * p.n), 4 * p.n⟩, below (t.gpr .rsp) stack],
      r ∈ (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
      [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (no + j * p.n), 4 * p.n⟩, below (t.gpr .rsp) stack] := fun _ h => h
  have hlanes : ∀ k < 4, Region.Sub ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ ⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ :=
    fun k _ => Offset.sub S (by omega) (by omega)
  have f₂' : Frame ((List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
      [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (no + j * p.n), 4 * p.n⟩, below (t.gpr .rsp) stack]) t₁.mem t₂.mem := by
    refine f₂.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), hlanes k hk⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨below (t.gpr .rsp) stack, by simp, by rw [hsp₁]; exact fun _ h => h⟩
  have hfr : Frame ((List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
      [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (no + j * p.n), 4 * p.n⟩, below (t.gpr .rsp) stack]) t.mem t₃.mem :=
    frame_trans3 lf₁ f₂' o.frame (fun r hr => List.mem_append_left _ hr) (fun _ h => h)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
  -- what the group keeps: the table and the lanes' `PK.seed` and `a16`
  have hd : ∀ {o l : Nat}, ((1600 ≤ o ∧ o + l ≤ 2368) ∨ (∃ k < 4, (Layout.laneA k ≤ o ∧ o + l ≤ Layout.laneA k + p.n + 16) ∨
      (Layout.laneB k ≤ o ∧ o + l ≤ Layout.laneB k + p.n + 16))) →
      ∀ r ∈ (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
        [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (no + j * p.n), 4 * p.n⟩, below (t.gpr .rsp) stack],
      Region.Disjoint ⟨at' S o, l⟩ r := fun {o l} hk r hr => by
    obtain ⟨hb₁, hb₂, hb₃⟩ : 1600 ≤ o ∧ o + l ≤ 10480 ∧ (o + l ≤ 2368 ∨ 3296 ≤ o) := by
      rcases hk with ⟨h₁, h₂⟩ | ⟨k, hk, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · omega
      · rw [hLA] at h₁ h₂; omega_using [h₁, h₂, hk, hn32]
      · rw [hLB] at h₁ h₂; omega_using [h₁, h₂, hk, hn32]
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨k', hk', rfl⟩ := hr
      refine disj_scr S ?_ (by omega) (by rw [hLA]; omega_using [hk', hn32])
      rcases hk with ⟨h₁, h₂⟩ | ⟨k, hk, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · rw [hLA]; omega
      · rw [hLA] at h₁ h₂ ⊢
        rcases Nat.lt_trichotomy k k' with hkk | rfl | hkk
        · left; omega_using [hkk, h₂, hn32]
        · left; omega_using [h₂]
        · right; omega_using [hkk, h₁, hn32]
      · rw [hLB] at h₁ h₂; rw [hLA]; right; omega_using [hk, hk', h₁, hn32]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint_base S hb₁ (by omega)
      · exact disj_scr S (by omega) (by omega) (by omega)
      · exact disj_scr S (.inl (by omega_using [hno, hb₂])) (by omega) (by omega_using [hjn])
      · exact (hstk.sub_right (sub_scr S (by omega))).symm
  have hA : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt t₃.mem (at' S (Layout.laneA k + o)) l = bytesAt t.mem (at' S (Layout.laneA k + o)) l :=
    fun k hk o l h => bytesAt_congr fun i hi =>
      hfr.bytes (R := ⟨at' S (Layout.laneA k + o), l⟩) (hd (.inr ⟨k, hk, .inl ⟨by omega, by omega⟩⟩)) (show l ≤ 2 ^ 64 by omega) hi
  have hB : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt t₃.mem (at' S (Layout.laneB k + o)) l = bytesAt t.mem (at' S (Layout.laneB k + o)) l :=
    fun k hk o l h => bytesAt_congr fun i hi =>
      hfr.bytes (R := ⟨at' S (Layout.laneB k + o), l⟩) (hd (.inr ⟨k, hk, .inr ⟨by omega, by omega⟩⟩)) (show l ≤ 2 ^ 64 by omega) hi
  have hE₃ : Env p t₃.mem S pkSeed a16 := by
    refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hE.rc r hr k hk]
      exact hfr.readW (r := ⟨at' S (1600 + 32 * r + 8 * k), 8⟩) (Region.contains_self _ _)
        (hd (.inl ⟨by omega, by omega⟩)) (by decide)
    · rw [← hE.seedA k hk, ← Nat.add_zero (Layout.laneA k), hA k hk 0 p.n (by omega)]
    · rw [← hE.seedB k hk, ← Nat.add_zero (Layout.laneB k), hB k hk 0 p.n (by omega)]
    · rw [← hE.adrsA k hk, hA k hk p.n 16 (by omega)]
    · rw [← hE.adrsB k hk, hB k hk p.n 16 (by omega)]
  refine ⟨fun g hg => ?_, o.bp, o.cf, by rw [o.rd, rd₂, l.rd], by rw [o.wr, wr₂, l.wr], by rw [mx₃, mx₂, mx₁],
    hE₃, fun k hk => ?_, hfr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [o.gpr _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by simp),
        l.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · have e₃ : bytesAt t₃.mem (at' S (no + (j + k) * p.n)) p.n = bytesAt t₂.mem (at' S (Layout.laneA k + p.n + 32)) p.n :=
      bytesAt_eq (by simp [bytesAt]) fun i hi => by
        rw [getD_bytesAt _ _ hi, at_add, at_add]; exact o.out k hk i hi
    rw [e₃, out₂ k hk, lane_bytes hn hE ha l hk, H_shake hf, twice_mul]

/-! ## The level loop -/

/-- The fields and messages of the lanes `A`. -/
abbrev lanesR (p : Params) (S : Addr) : List Region :=
  (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region))

/-- A frame with one region widened. -/
theorem frame_widen {A : List Region} {a b x y X : Region} {m m' : Mem} (h : Frame (A ++ [a, b, x, X]) m m')
    (hs : Region.Sub x y) : Frame (A ++ [a, b, y, X]) m m' :=
  h.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨r, by simp, fun _ h => h⟩
      · exact ⟨r, by simp, fun _ h => h⟩
      · exact ⟨y, by simp, hs⟩
      · exact ⟨r, by simp, fun _ h => h⟩

/-- The variables of frame 4 (below the lanes `A`) across such a frame. -/
theorem keep_low (hn32 : p.n ≤ 32) {m m' : Mem} {S sp : Addr} {stack c d : Nat}
    (hfr : Frame (lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S c, d⟩, below sp stack]) m m')
    (hc : 3296 ≤ c) (hcd : c + d ≤ 2 ^ 16) (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) {o : Nat}
    (ho : 2400 ≤ o) (ho' : o + 8 ≤ 3296) : m'.readW (at' S o) 64 = m.readW (at' S o) 64 := by
  refine hfr.readW (r := ⟨at' S o, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · simp only [lanesR, List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    have : 3296 ≤ Layout.laneA k ∧ Layout.laneA k + 128 ≤ 3808 := laneA_le k hk
    exact disj_scr S (.inl (by omega)) (by omega) (by omega_using [this, hk, hn32])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact disj_scr S (.inr (by omega)) (by omega) (by omega)
    · exact disj_scr S (.inl (by omega)) (by omega) hcd
    · exact (hstk.sub_right (sub_scr S (by omega))).symm

/-- What a height's level loop does: nodes `0` to `P - 1` of height `z + 1`. -/
structure LevelPost (p : Params) (S : Addr) (stack : Nat) (pkSeed a16 : List Byte) (t t' : State)
    (no z P ty kp x : Nat) : Prop where
  keep : ∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  mx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10
  env : Env p t'.mem S pkSeed a16
  node : ∀ q < P, bytesAt t'.mem (at' S (no + q * p.n)) p.n =
    H p pkSeed (nodeAdrs a16 ty kp (z + 1) (x + q)) (bytesAt t.mem (at' S (no + 2 * q * p.n)) (2 * p.n))
  frame : Frame (lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, (P + 3) * p.n⟩, below (t.gpr .rsp) stack])
    t.mem t'.mem

theorem level_ok (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S : Addr} {no z P : Nat} {V6 V7 V8 : BitVec 64} {pkSeed a16 : List Byte} {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (h14 : t.gpr .r14 = BitVec.ofNat 64 z)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 0) (h15 : t.gpr .r15 = BitVec.ofNat 64 P) (hz : z < 14)
    (hP1 : 1 ≤ P) (hP : P ≤ 2 ^ 13) (hno : 12640 ≤ no) (hcap : no + (2 * P + 8) * p.n ≤ 2 ^ 16)
    (h6 : t.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6) (h7 : t.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7)
    (h8 : t.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8) (hV6 : V6.toNat < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hE : Env p t.mem S pkSeed a16)
    (ha : a16.length = 16) :
    WP isa (.loop (levelBody ⟨p.n, p.len⟩ name T.code) .b) t fun t' =>
      LevelPost p S stack pkSeed a16 t t' no z P V7.toNat V8.toNat (V6.toNat / 2 ^ (z + 1)) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = P - 4 * i ∧ 4 * i < P ∧
    (∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], s.gpr g = t.gpr g) ∧ s.gpr .rbp = BitVec.ofNat 64 (4 * i) ∧
    s.rd = t.rd ∧ s.wr = t.wr ∧ s.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
    Env p s.mem S pkSeed a16 ∧
    (∀ q < 4 * i, bytesAt s.mem (at' S (no + q * p.n)) p.n =
      H p pkSeed (nodeAdrs a16 V7.toNat V8.toNat (z + 1) (V6.toNat / 2 ^ (z + 1) + q))
        (bytesAt t.mem (at' S (no + 2 * q * p.n)) (2 * p.n))) ∧
    Frame (lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, 4 * i * p.n⟩, below (t.gpr .rsp) stack]) t.mem s.mem
  refine WP.loop (M := isa) Inv (fun m s hI => ?_) P t ⟨0, by omega, by omega, fun _ _ => rfl, hbp, rfl, rfl, rfl, hE,
    fun q hq => absurd hq (by omega), Frame.refl _ _⟩
  obtain ⟨i, rfl, hi, hg, hbp', hrd, hwr, hmx, hEs, hnodes, hfs⟩ := hI
  have hcap' : (2 * (4 * i) + 8) * p.n ≤ (2 * P + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hin : (4 * i + 4) * p.n ≤ (P + 3) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hkeep : ∀ o, 2400 ≤ o → o + 8 ≤ 3296 → s.mem.readW (at' S o) 64 = t.mem.readW (at' S o) 64 :=
    fun o h₁ h₂ => keep_low hn32 hfs (by omega) (by grind) hstk h₁ h₂
  refine WP.mono (group_ok T name hn hf hst hs63 (j := 4 * i) (P := P) (V6 := V6) (V7 := V7) (V8 := V8)
    (by rw [hg .rbx (by simp), hbx]) (by rw [hg .r12 (by simp), h12]) (by rw [hg .r14 (by simp), h14]) hbp'
    (by rw [hg .r15 (by simp), h15]) hz (by omega) (by omega) hno (by grind)
    (by rw [hkeep _ (by rw [hv]; omega) (by rw [hv]; omega), h6])
    (by rw [hkeep _ (by rw [hv]; omega) (by rw [hv]; omega), h7])
    (by rw [hkeep _ (by rw [hv]; omega) (by rw [hv]; omega), h8]) hV6 (by rw [hwr]; exact hw) hS
    (by rw [hg .rsp (by simp)]; exact hstk) hEs ha) fun s' gp => ?_
  have gfr := gp.frame
  rw [hg .rsp (by simp)] at gfr
  -- the nodes so far
  have hnew : ∀ q < 4 * i + 4, bytesAt s'.mem (at' S (no + q * p.n)) p.n =
      H p pkSeed (nodeAdrs a16 V7.toNat V8.toNat (z + 1) (V6.toNat / 2 ^ (z + 1) + q))
        (bytesAt t.mem (at' S (no + 2 * q * p.n)) (2 * p.n)) := by
    intro q hq
    by_cases hqi : q < 4 * i
    · have hqn : (q + 1) * p.n ≤ 4 * i * p.n := Nat.mul_le_mul_right _ (by omega)
      rw [← hnodes q hqi]
      refine bytesAt_congr fun b hb => gfr.bytes (R := ⟨at' S (no + q * p.n), p.n⟩) (fun r hr => ?_)
        (show p.n ≤ 2 ^ 64 by omega) hb
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_map, List.mem_range] at hr
        obtain ⟨k, hk, rfl⟩ := hr
        have := laneA_le k hk
        exact disj_scr S (.inr (by omega)) (by grind) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Offset.disjoint_base S (by omega) (by grind)
        · exact disj_scr S (.inr (by omega)) (by grind) (by omega)
        · exact disj_scr S (.inl (by grind)) (by grind) (by grind)
        · exact (hstk.sub_right (sub_scr S (by grind))).symm
    · obtain ⟨k, rfl⟩ : ∃ k, q = 4 * i + k := ⟨q - 4 * i, by omega⟩
      have hk : k < 4 := by omega
      have hrd : (2 * (4 * i + k) + 2) * p.n ≤ (2 * P + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
      have hlo : 4 * i * p.n ≤ 2 * (4 * i + k) * p.n := Nat.mul_le_mul_right _ (by omega)
      rw [gp.node k hk, Nat.add_assoc (V6.toNat / 2 ^ (z + 1))]
      congr 1
      refine bytesAt_congr fun b hb => hfs.bytes (R := ⟨at' S (no + 2 * (4 * i + k) * p.n), 2 * p.n⟩)
        (fun r hr => ?_) (show 2 * p.n ≤ 2 ^ 64 by omega) hb
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_map, List.mem_range] at hr
        obtain ⟨k', hk', rfl⟩ := hr
        have := laneA_le k' hk'
        exact disj_scr S (.inr (by omega)) (by grind) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Offset.disjoint_base S (by omega) (by grind)
        · exact disj_scr S (.inr (by omega)) (by grind) (by omega)
        · exact disj_scr S (.inr (by grind)) (by grind) (by grind)
        · exact (hstk.sub_right (sub_scr S (by grind))).symm
  have hfr : ∀ c, 4 * i * p.n + 4 * p.n ≤ c → no + c ≤ 2 ^ 16 →
      Frame (lanesR p S ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S no, c⟩, below (t.gpr .rsp) stack]) t.mem s'.mem :=
    fun c hc _ => (frame_widen hfs (Offset.sub S (by omega) (by omega))).trans
      (frame_widen (y := ⟨at' S no, c⟩) gfr (Offset.sub S (by omega) (by grind)))
  have hgs : ∀ g ∈ [Reg.rbx, .r12, .r13, .r14, .r15, .rsp], s'.gpr g = t.gpr g := fun g h' => by
    rw [gp.keep g h', hg g h']
  by_cases hc : 4 * i + 4 < P
  · refine .inr ⟨by show s'.cf = _; rw [gp.cf]; simp [hc], P - 4 * (i + 1), by omega, i + 1, rfl, by omega, hgs,
      by rw [gp.bp]; rfl, by rw [gp.rd, hrd], by rw [gp.wr, hwr], by rw [gp.mx, hmx], gp.env,
      fun q hq => hnew q (by omega), hfr _ (by grind) (by grind)⟩
  · refine .inl ⟨by show s'.cf = _; rw [gp.cf]; simp [hc], hgs, by rw [gp.rd, hrd], by rw [gp.wr, hwr],
      by rw [gp.mx, hmx], gp.env, fun q hq => hnew q (by omega), hfr _ (by grind) (by grind)⟩

end VG.Proof.SlhDsa.X86_64.Levels
